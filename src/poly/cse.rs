use super::{ConstrDecomp, Expr, HashResult, SignalFactory, VarAssignments};
use crate::field::Field;
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{collections::HashMap, fmt::Debug, hash::Hash};

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

pub type ExprMap<F, V> = HashMap<u64, Expr<F, V, HashResult>>;
pub type CountMap = HashMap<u64, u32>;

/// Common Subexpression Elimination - takes a collection of expressions
/// and returns a collection of common subexpressions and variable assignments.
///
/// # Parameters
///
/// - `exprs`: A slice of expressions to analyze.
/// - `queriables`: A slice of variables that can be queried.
/// - `config`: Optional configuration for the minimum degree and occurrences.
///
/// # Returns
///
/// A tuple containing a vector of common expressions and variable assignments.
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: &[Expr<F, V, ()>],
    queriables: &[V],
    config: Option<Config>,
) -> (Vec<CommonExpr<F, V>>, VarAssignments<F, V>) {
    let config = config.unwrap_or_default();
    let min_degree = config.min_degree.unwrap_or(2);
    let min_occurrences = config.min_occurrences.unwrap_or(2);

    let assignments = generate_random_assignment(queriables);

    let mut seen_hashes: ExprMap<F, V> = HashMap::new();
    let mut all_hashed_exprs: Vec<Expr<F, V, HashResult>> = Vec::new();

    for expr in exprs {
        let subexprs = hash_recursive(expr, &assignments, &mut seen_hashes, min_degree);
        all_hashed_exprs.extend(subexprs);
    }

    let expr_count = count_expression_occurrences(&all_hashed_exprs);
    let common_exprs = collect_common_expressions(&seen_hashes, &expr_count, min_occurrences);

    (common_exprs, assignments)
}

fn count_expression_occurrences<F, V>(hashed_exprs: &[Expr<F, V, HashResult>]) -> CountMap {
    let mut expr_count = HashMap::new();
    for hashed_expr in hashed_exprs {
        let hash = hashed_expr.meta().hash;
        *expr_count.entry(hash).or_insert(0) += 1;
    }
    expr_count
}

fn collect_common_expressions<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    seen_hashes: &ExprMap<F, V>,
    expr_count: &CountMap,
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

fn hash_recursive<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    expr: &Expr<F, V, ()>,
    assignments: &VarAssignments<F, V>,
    seen_hashes: &mut ExprMap<F, V>,
    min_degree: usize,
) -> Vec<Expr<F, V, HashResult>> {
    let mut hashed_exprs = Vec::new();
    hash_and_collect(
        expr,
        assignments,
        seen_hashes,
        min_degree,
        &mut hashed_exprs,
    );
    hashed_exprs
}

fn hash_and_collect<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    expr: &Expr<F, V, ()>,
    assignments: &VarAssignments<F, V>,
    seen_hashes: &mut ExprMap<F, V>,
    min_degree: usize,
    hashed_exprs: &mut Vec<Expr<F, V, HashResult>>,
) {
    let hashed_expr = expr.hash(assignments);

    if !matches!(expr, Expr::Const(_, _) | Expr::Query(_, _)) {
        let hash = hashed_expr.meta().hash;
        seen_hashes
            .entry(hash)
            .or_insert_with(|| hashed_expr.clone());
    }

    hashed_exprs.push(hashed_expr.clone());

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

fn generate_random_assignment<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    queriables: &[V],
) -> VarAssignments<F, V> {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    queriables
        .iter()
        .cloned()
        .map(|q| (q, F::random(&mut rng)))
        .collect()
}

pub fn replace_common_subexprs<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    constr: Expr<F, V, ()>,
    common_ses: &[CommonExpr<F, V>],
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
    common_ses: &[CommonExpr<F, V>],
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V, ()> {
    // Check if the expression is a common subexpression
    if let Some(_common_expr) = common_ses
        .iter()
        .find(|ce| constr.hash(assignments).meta().hash == ce.expr.meta().hash)
    {
        // If it is, check if the signal already exists
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
            let new_signal = signal_factory.create("cse");
            decomp.auto_eq(new_signal.clone(), constr);
            Expr::Query(new_signal, ())
        }
    } else {
        // Otherwise, replace the subexpressions recursively
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
    use crate::{
        poly::{Expr::*, ToExpr},
        sbpir::{query::Queriable, ForwardSignal, InternalSignal},
    };
    use halo2_proofs::halo2curves::bn256::Fr;
    use std::collections::HashSet;

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

        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "((e)^6 * a * b)"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr)
                == "((f * b) + (-(forward * next(forward))) + (-0x1))"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(-(forward * next(forward)))"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "((-((-f) * g)) * (-a))"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(f * b)"));
        assert!(common_ses.iter().any(|cse| format!("{:#?}", cse.expr)
            == "(((e)^6 * a * b) + (forward * next(forward)) + (-0x1))"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(-0x1)"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(e)^6"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(a * b)"));
        assert!(common_ses
            .iter()
            .any(|cse| format!("{:#?}", cse.expr) == "(forward * next(forward))"));
    }

    #[derive(Default)]
    struct TestSignalFactory {
        counter: usize,
    }

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, _annotation: S) -> Queriable<Fr> {
            self.counter += 1;
            Queriable::Internal(InternalSignal::new(format!("cse-{}", self.counter)))
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

        let exprs = vec![
            expr1.clone(),
            expr2.clone(),
            expr3.clone(),
            expr4.clone(),
            expr5.clone(),
        ];

        let (common_ses, assignments) = cse(&exprs, &vars, None);

        let mut decomp = ConstrDecomp::default();
        let signal_factory = &mut TestSignalFactory::default();

        for expr in exprs {
            decomp.constrs.push(expr.clone());
            replace_common_subexprs_rec(
                &mut decomp,
                expr,
                &common_ses,
                &assignments,
                signal_factory,
            );
        }

        // Assert that there are 6 common subexpressions
        assert_eq!(common_ses.len(), 6);

        // Assert that there are only 2 auto signals created
        // Because the other are inner expressions inside a bigger common one
        assert_eq!(
            decomp
                .auto_signals
                .iter()
                .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr)
                    == "cse-1: (((e)^6 * a * b) + (forward * next(forward)) + (-0x1))"),
            true
        );
        assert_eq!(
            decomp
                .auto_signals
                .iter()
                .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "cse-2: (a * b)"),
            true
        );
    }
}
