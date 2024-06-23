use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use crate::field::Field;

use std::{collections::HashMap, fmt::Debug, hash::Hash};

use super::{ConstrDecomp, Expr, HashResult, SignalFactory, VarAssignments};

#[derive(Debug, Clone)]
pub struct CommonExpr<F, V> {
    pub expr: Expr<F, V, HashResult>,
    pub count: usize,
}

#[derive(Debug, Clone)]
pub struct Config {
    pub min_degree: Option<usize>,
    pub min_occurrences: Option<usize>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            min_degree: Some(2),
            min_occurrences: Some(2),
        }
    }
}

/// Common Subexpression Elimination - takes a collection of expr
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: &Vec<Expr<F, V, ()>>,
    queriables: &Vec<V>,
    config: Option<Config>,
) -> (Vec<CommonExpr<F, V>>, VarAssignments<F, V>) {
    // Determine the minimum degree, defaulting to 2 if not provided
    let config = config.unwrap_or_default();
    let min_degree = config.min_degree.unwrap_or(2);
    let min_occurrences = config.min_occurrences.unwrap_or(2);

    // generate random point in the field set
    let assignments = generate_random_assignment(queriables);

    // hash table with the hash of the expression as the key
    // and the weak reference to the expression as the value
    let mut seen_hashes: HashMap<u64, Expr<F, V, HashResult>> = HashMap::new();
    let mut all_hashed_exprs: Vec<Expr<F, V, HashResult>> = Vec::new();

    // Hash expressions recursively and collect all subexpressions
    for expr in exprs {
        let subexprs = hash_recursive(expr, &assignments, &mut seen_hashes, min_degree);
        all_hashed_exprs.extend(subexprs);
    }

    // count how many times each expression appears
    let expr_count = count_expression_occurrences(&all_hashed_exprs);

    // Collect common expressions
    let common_exprs = collect_common_expressions(&seen_hashes, &expr_count, min_occurrences);

    (common_exprs, assignments)
}

/// Counts how many times each hashed expression appears.
fn count_expression_occurrences<F, V>(
    hashed_exprs: &Vec<Expr<F, V, HashResult>>,
) -> HashMap<u64, u32> {
    let mut expr_count = HashMap::new();
    for hashed_expr in hashed_exprs {
        let hash = hashed_expr.meta().hash;
        let count = expr_count.entry(hash).or_insert(0);
        *count += 1;
    }
    expr_count
}

/// Collects common expressions into a vector of CommonExpr.
fn collect_common_expressions<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    seen_hashes: &HashMap<u64, Expr<F, V, HashResult>>,
    expr_count: &HashMap<u64, u32>,
    min_occurrences: usize,
) -> Vec<CommonExpr<F, V>> {
    seen_hashes
        .iter()
        .filter_map(|(&hash, expr)| {
            expr_count
                .get(&hash)
                .filter(|&&count| count >= min_occurrences as u32)
                .map(|&count| CommonExpr {
                    expr: expr.clone(),
                    count: count as usize,
                })
        })
        .collect()
}

/// Recursive function to hash expressions and sub-expressions
fn hash_recursive<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    expr: &Expr<F, V, ()>,
    assignments: &VarAssignments<F, V>,
    seen_hashes: &mut HashMap<u64, Expr<F, V, HashResult>>,
    min_degree: usize,
) -> Vec<Expr<F, V, HashResult>> {
    let mut hashed_exprs = Vec::new();

    fn hash_and_collect<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
        expr: &Expr<F, V, ()>,
        assignments: &VarAssignments<F, V>,
        seen_hashes: &mut HashMap<u64, Expr<F, V, HashResult>>,
        min_degree: usize,
        hashed_exprs: &mut Vec<Expr<F, V, HashResult>>,
    ) {
        let hashed_expr = expr.hash(assignments);

        // Insert the hashed expression into the seen_hashes if not already present,
        // but skip if the expression is a Const or Query
        if !matches!(expr, Expr::Const(_, _) | Expr::Query(_, _)) {
            let hash = hashed_expr.meta().hash;
            seen_hashes
                .entry(hash)
                .or_insert_with(|| hashed_expr.clone());
        }

        // Add the hashed expression to the list of all hashed expressions
        hashed_exprs.push(hashed_expr.clone());

        // Recur for sub-expressions if the degree is above the minimum threshold
        if expr.degree() >= min_degree {
            match expr {
                Expr::Sum(ses, _) | Expr::Mul(ses, _) => {
                    for se in ses {
                        hash_and_collect(se, assignments, seen_hashes, min_degree, hashed_exprs);
                    }
                }
                Expr::Neg(se, _) | Expr::Pow(se, _, _) | Expr::MI(se, _) => {
                    hash_and_collect(se, assignments, seen_hashes, min_degree, hashed_exprs);
                }
                _ => {}
            }
        }
    }

    hash_and_collect(
        expr,
        assignments,
        seen_hashes,
        min_degree,
        &mut hashed_exprs,
    );

    hashed_exprs
}

fn generate_random_assignment<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    queriables: &Vec<V>,
) -> VarAssignments<F, V> {
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut assignments = HashMap::new();

    for queriable in queriables {
        let value = F::random(&mut rng);
        assignments.insert(queriable.clone(), value);
    }

    assignments
}

pub fn replace_common_subexprs<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    constr: Expr<F, V, ()>,
    common_ses: &Vec<CommonExpr<F, V>>,
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> (Expr<F, V, ()>, ConstrDecomp<F, V>) {
    let mut decomp = ConstrDecomp::default();
    let expr =
        replace_common_subexprs_rec(&mut decomp, constr, common_ses, assignments, signal_factory);

    (expr, decomp)
}

fn replace_common_subexprs_rec<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V, ()>,
    common_ses: &Vec<CommonExpr<F, V>>,
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V, ()> {
    // check if the expression is a common subexpression
    if let Some(_common_expr) = common_ses
        .iter()
        .find(|ce| constr.hash(assignments).meta().hash == ce.expr.meta().hash)
    {
        // if it is
        // check if the signal already exists
        // if it does, return the signal
        // otherwise, create a new signal
        let hash = constr.hash(assignments).meta().hash;
        if let Some(signal) = decomp.auto_signals.iter().find_map(|(signal, expr)| {
            if expr.hash(assignments).meta().hash == hash {
                Some(signal.clone())
            } else {
                None
            }
        }) {
            Expr::Query(signal, ())
        } else {
            let signal_key = format!("cse-{}", hash);
            let new_signal = signal_factory.create(signal_key);
            decomp.auto_signals.insert(new_signal.clone(), constr);
            Expr::Query(new_signal, ())
        }
    } else {
        // otherwise, replace the subexpressions recursively
        match constr {
            Expr::Sum(ses, meta) => {
                let new_ses = ses
                    .into_iter()
                    .map(|se| {
                        replace_common_subexprs_rec(
                            decomp,
                            se,
                            common_ses,
                            assignments,
                            signal_factory,
                        )
                    })
                    .collect();
                Expr::Sum(new_ses, meta)
            }
            Expr::Mul(ses, meta) => {
                let new_ses = ses
                    .into_iter()
                    .map(|se| {
                        replace_common_subexprs_rec(
                            decomp,
                            se,
                            common_ses,
                            assignments,
                            signal_factory,
                        )
                    })
                    .collect();
                Expr::Mul(new_ses, meta)
            }
            Expr::Neg(se, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::Neg(Box::new(new_se), meta)
            }
            Expr::Pow(se, n, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::Pow(Box::new(new_se), n, meta)
            }
            Expr::MI(se, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::MI(Box::new(new_se), meta)
            }
            _ => constr,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        poly::{Expr::*, ToExpr},
        sbpir::{query::Queriable, ForwardSignal, InternalSignal},
    };

    #[test]
    fn test_generate_random_assignment() {
        let internal = InternalSignal::new("internal");
        let forward = ForwardSignal::new("forward");

        let a: Queriable<Fr> = Queriable::Internal(internal);
        let b: Queriable<Fr> = Queriable::Forward(forward, false);
        let c: Queriable<Fr> = Queriable::Forward(forward, true);

        let vars = vec![a, b, c];

        let keys: HashSet<Queriable<Fr>> = vars.iter().cloned().collect();

        let assignments: VarAssignments<Fr, Queriable<Fr>> = generate_random_assignment(&vars);

        println!("Assignments: {:#?}", assignments);

        for key in &keys {
            assert!(assignments.contains_key(key));
        }
    }

    #[test]
    fn test_cse() {
        let forward = ForwardSignal::new("forward");

        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Forward(forward, false);
        let d: Queriable<Fr> = Queriable::Forward(forward, true);
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));
        let vars = vec![a, b, c, d, e, f, g];

        // Equivalent expressions
        let expr1 = Pow(Box::new(e.expr()), 6, ()) * a * b + c * d - 1.expr();
        let expr2 = d * c - 1.expr() + a * b * Pow(Box::new(e.expr()), 6, ());

        // Equivalent expressions
        let expr3 = f * b - c * d - 1.expr();
        let expr4 = -(1.expr()) - c * d + b * f;

        // Equivalent expressions
        let expr5 = -(-f * g) * (-(-(-a)));
        let expr6 = -(f * g * a);

        // Different expressions with the same sub-expressions
        let expr7 = a * b + b * a;
        let expr8 = b * a + 3.expr();

        let exprs = vec![expr1, expr2, expr3, expr4, expr5, expr6, expr7, expr8];

        let (common_ses, _) = cse(&exprs, &vars, None);

        print!("{:#?}", common_ses);
    }

    #[derive(Default)]
    struct TestSignalFactory {}

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, annotation: S) -> Queriable<Fr> {
            Queriable::Internal(InternalSignal::new(annotation))
        }
    }

    #[test]
    fn test_replace_common_ses() {
        let forward = ForwardSignal::new("forward");

        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Forward(forward, false);
        let d: Queriable<Fr> = Queriable::Forward(forward, true);
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));
        let vars = vec![a, b, c, d, e, f, g];

        // Equivalent expressions
        let expr1 = Pow(Box::new(e.expr()), 6, ()) * a * b + c * d - 1.expr();
        let expr2 = d * c - 1.expr() + a * b * Pow(Box::new(e.expr()), 6, ());

        let expr3 = a + b;

        // Different expressions with the same sub-expressions
        let expr4 = a * b + b * a;
        let expr5 = b * a + 3.expr();

        let exprs = vec![expr1.clone(), expr2.clone(), expr3.clone(), expr4.clone(), expr5.clone()];

        let (common_ses, assignments) = cse(&exprs, &vars, None);

        println!("{:#?}", common_ses);

        let mut decomp = ConstrDecomp::default();

        let signal_factory = &mut TestSignalFactory::default();

        for expr in exprs {
            decomp.constrs.push(expr.clone());
            let result = replace_common_subexprs_rec(
                &mut decomp,
                expr,
                &common_ses,
                &assignments,
                signal_factory,
            );

            println!("Result: {:#?}", result);
        }

        println!("Decomp: {:#?}", decomp);
    }
}
