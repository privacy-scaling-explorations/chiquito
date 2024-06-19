use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use crate::field::Field;

use std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    rc::{Rc, Weak},
};

use super::{ConstrDecomp, Expr, HashResult, SignalFactory, VarAssignments};

/// Common Subexpression Elimination - takes a collection of expr
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: &Vec<Expr<F, V, ()>>,
    queriables: &Vec<V>,
) -> (Vec<Rc<Expr<F, V, HashResult>>>, VarAssignments<F, V>) {
    // generate random point in the field set
    let assignments = generate_random_assignment(queriables);

    // hash table with the hash of the expression as the key
    // and the weak reference to the expression as the value
    let mut seen_hashes: HashMap<u64, Weak<Expr<F, V, HashResult>>> = HashMap::new();

    let mut result = Vec::new();

    for expr in exprs {
        let hashed_expr = Rc::new(expr.hash(&assignments));
        let hash = hashed_expr.meta().hash;

        // if the hash is already in the hash table,
        // push the existing expression to the result
        if let Some(existing_weak) = seen_hashes.get(&hash) {
            if let Some(existing_expr) = existing_weak.upgrade() {
                result.push(existing_expr);
                continue;
            }
        }

        // otherwise, insert the hash and the weak reference to the expression
        seen_hashes.insert(hash, Rc::downgrade(&hashed_expr));
        result.push(hashed_expr);
    }

    (result, assignments)
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
    hashed_exprs: &Vec<Rc<Expr<F, V, HashResult>>>,
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> (Expr<F, V, ()>, ConstrDecomp<F, V>) {
    let mut decomp = ConstrDecomp::default();
    let expr = replace_common_subexprs_rec(
        &mut decomp,
        constr,
        hashed_exprs,
        assignments,
        signal_factory,
    );

    (expr, decomp)
}

fn replace_common_subexprs_rec<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V, ()>,
    hashed_exprs: &Vec<Rc<Expr<F, V, HashResult>>>,
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V, ()> {
    // find the expression on the hashed_exprs and count the occurrences for the Rc<Expr<F, V,
    // HashResult>>
    let hashed_constr = constr.hash(assignments);
    if let Some(matched_expr) = hashed_exprs
        .into_iter()
        .find(|expr| expr.meta().hash == hashed_constr.meta().hash)
    {
        // if the expression is found and the occurrences are greater than 1
        // check if there is already a signal for the expression
        // create a new signal and add the expression to the decomp
        // replace the expression with the new signal
        // if the expression is not found or the occurrences are 1
        // recursively call the function for each subexpression
        // and return the new expression
        if Rc::strong_count(matched_expr) > 1 {
            // TODO: check if there is already a signal for the expression
            // if there is, use the signal
            // if there isn't, create a new signal
            // add the expression to the decomp
            // replace the expression with the new signal
            let signal =
                if let Some(auto_signal) = decomp.auto_signals.iter().find(|(_, expr)| {
                    matched_expr.meta().hash == expr.hash(assignments).meta().hash
                }) {
                    auto_signal.0.clone()
                } else {
                    let new_signal = signal_factory.create("cse");
                    decomp.auto_eq(new_signal.clone(), constr);
                    new_signal
                };

            return Expr::Query(signal, ());
        }
    }

    match constr {
        Expr::Const(_, _) | Expr::Query(_, _) => constr,
        Expr::Halo2Expr(_, _) => unimplemented!(),
        Expr::Sum(ses, _) => Expr::Sum(
            ses.into_iter()
                .map(|se| {
                    replace_common_subexprs_rec(
                        decomp,
                        se,
                        hashed_exprs,
                        assignments,
                        signal_factory,
                    )
                })
                .collect(),
            (),
        ),
        Expr::Mul(ses, _) => Expr::Mul(
            ses.into_iter()
                .map(|se| {
                    replace_common_subexprs_rec(
                        decomp,
                        se,
                        hashed_exprs,
                        assignments,
                        signal_factory,
                    )
                })
                .collect(),
            (),
        ),
        Expr::Neg(se, _) => Expr::Neg(
            Box::new(replace_common_subexprs_rec(
                decomp,
                *se,
                hashed_exprs,
                assignments,
                signal_factory,
            )),
            (),
        ),
        Expr::Pow(se, exp, _) => Expr::Pow(
            Box::new(replace_common_subexprs_rec(
                decomp,
                *se,
                hashed_exprs,
                assignments,
                signal_factory,
            )),
            exp,
            (),
        ),
        Expr::MI(se, _) => Expr::MI(
            Box::new(replace_common_subexprs_rec(
                decomp,
                *se,
                hashed_exprs,
                assignments,
                signal_factory,
            )),
            (),
        ),
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

        let exprs = vec![expr1, expr2, expr3, expr4, expr5, expr6];

        let (result, _) = cse(&exprs, &vars);

        assert!(Rc::ptr_eq(&result[0], &result[1]));
        assert!(Rc::ptr_eq(&result[2], &result[3]));
        assert!(Rc::ptr_eq(&result[4], &result[5]));
        assert!(!Rc::ptr_eq(&result[0], &result[2]));
        assert!(!Rc::ptr_eq(&result[0], &result[4]));
        assert!(!Rc::ptr_eq(&result[2], &result[4]));

        println!("Count occurrences of each expression:");
        println!("{:#?}", Rc::strong_count(&result[0]));
    }

    #[derive(Default)]
    struct TestSignalFactory {
        counter: u32,
    }

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, _annotation: S) -> Queriable<Fr> {
            self.counter += 1;

            Queriable::Internal(InternalSignal::new(format!("cse{}", self.counter)))
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

        let exprs = vec![expr1.clone(), expr2.clone(), expr3.clone()];

        let (hashed_exprs, assignments) = cse(&exprs, &vars);

        println!("{:#?}", hashed_exprs);

        let mut decomp = ConstrDecomp::default();

        let signal_factory = &mut TestSignalFactory::default();

        let result1 = replace_common_subexprs_rec(
            &mut decomp,
            expr1,
            &hashed_exprs,
            &assignments,
            signal_factory,
        );

        let result2 = replace_common_subexprs_rec(
            &mut decomp,
            expr2,
            &hashed_exprs,
            &assignments,
            signal_factory,
        );

        let result3 = replace_common_subexprs_rec(
            &mut decomp,
            expr3,
            &hashed_exprs,
            &assignments,
            signal_factory,
        );

        println!("{:#?}", hashed_exprs);

        println!("Result1: {:#?}", result1);
        println!("Result2: {:#?}", result2);
        println!("Result3: {:#?}", result3);

        println!("Decomp: {:#?}", decomp);
    }
}
