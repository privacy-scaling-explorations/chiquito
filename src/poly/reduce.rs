use std::{fmt::Debug, hash::Hash};

use crate::{
    field::Field,
    poly::{simplify::simplify_mul, Expr},
};

use super::{ConstrDecomp, SignalFactory};

/// Reduces the degree of an PI by decomposing it in many PI with a maximum degree.
pub fn reduce_degree<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    constr: Expr<F, V>,
    max_degree: usize,
    signal_factory: &mut SF,
) -> (Expr<F, V>, ConstrDecomp<F, V>) {
    let mut decomp = ConstrDecomp::default();
    let expr = reduce_degree_recursive(&mut decomp, constr, max_degree, max_degree, signal_factory);

    (expr, decomp)
}

/// Actual recursive implementation of `reduce_degre`. Key here to understand the difference
/// between:  + total_max_degree: maximum degree of the PI the input expression is decomposed of.
///  + partial_max_degree: maximum degree of the root PI, that can substitute the original
/// expression.
///
/// The value of `partial_max_degree` can be less than `total_max_degree` when this
/// function is called recursively on a PI sub-expression, so the resulting root PI can be included
/// in a "parent" PI with a degree that is smaller than the maximum. This is only done in
/// `reduce_degree_mul`: ```
/// let partial_max_degree = if first {
///     total_max_degree - 1
/// } else {
///    total_max_degree
/// };
/// ```
fn reduce_degree_recursive<
    F: Field,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V>,
    total_max_degree: usize,
    partial_max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    if constr.degree() <= partial_max_degree {
        return constr;
    }

    match constr {
        Expr::Const(_) => constr,
        Expr::Sum(ses) => Expr::Sum(
            ses.into_iter()
                .map(|se| {
                    reduce_degree_recursive(
                        decomp,
                        se,
                        total_max_degree,
                        partial_max_degree,
                        signal_factory,
                    )
                })
                .collect(),
        ),
        Expr::Mul(ses) => reduce_degree_mul(
            decomp,
            ses,
            total_max_degree,
            partial_max_degree,
            signal_factory,
        ),
        Expr::Neg(se) => Expr::Neg(Box::new(reduce_degree_recursive(
            decomp,
            *se,
            total_max_degree,
            partial_max_degree,
            signal_factory,
        ))),
        // TODO: decompose in Pow expressions instead of Mul
        Expr::Pow(se, exp) => reduce_degree_mul(
            decomp,
            std::vec::from_elem(*se, exp as usize),
            total_max_degree,
            partial_max_degree,
            signal_factory,
        ),
        Expr::Query(_) => constr,
        Expr::Halo2Expr(_) => unimplemented!(),
        Expr::MI(_) => unimplemented!(),
    }
}

fn reduce_degree_mul<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    decomp: &mut ConstrDecomp<F, V>,
    ses: Vec<Expr<F, V>>,
    total_max_degree: usize,
    partial_max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    // base case, if partial_max_degree == 1, the root expression can only be a variable
    if partial_max_degree == 1 {
        let reduction = reduce_degree_mul(
            decomp,
            ses,
            total_max_degree,
            total_max_degree,
            signal_factory,
        );
        let signal = signal_factory.create("virtual signal");
        decomp.auto_eq(signal.clone(), reduction);
        return Expr::Query(signal);
    }

    let ses = simplify_mul(ses);

    // to reduce the problem for recursion, at least one expression should have lower degree than
    // total_max_degree
    let mut first = true;
    let ses_reduced: Vec<Expr<F, V>> = ses
        .into_iter()
        .map(|se| {
            let partial_max_degree = if first {
                total_max_degree - 1
            } else {
                total_max_degree
            };
            let reduction = reduce_degree_recursive(
                decomp,
                se,
                total_max_degree,
                partial_max_degree,
                signal_factory,
            );
            first = false;

            reduction
        })
        .collect();

    // for_root will be multipliers that will be included in the root expression
    let mut for_root = Vec::default();
    // to_simplify will be multipliers that will be recursively decomposed and substituted by a
    // virtual signal in the root expression
    let mut to_simplify = Vec::default();

    let mut current_degree = 0;
    for se in ses_reduced {
        if se.degree() + current_degree < partial_max_degree {
            current_degree += se.degree();
            for_root.push(se);
        } else {
            to_simplify.push(se);
        }
    }

    assert!(!for_root.is_empty());

    if to_simplify.is_empty() {
        return Expr::Mul(for_root);
    }

    let rest_signal = signal_factory.create("rest_expr");
    for_root.push(Expr::Query(rest_signal.clone()));
    let root_expr = Expr::Mul(for_root);

    // recursion, for the part that exceeds the degree and will be substituted by a virtual signal
    let simplified = reduce_degree_recursive(
        decomp,
        Expr::Mul(to_simplify),
        total_max_degree,
        total_max_degree,
        signal_factory,
    );

    decomp.auto_eq(rest_signal, simplified);

    root_expr
}

#[cfg(test)]
mod test {
    use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};
    use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
    use std::collections::HashMap;

    use crate::{
        poly::{reduce::reduce_degree, ConstrDecomp, Expr::*, ToExpr},
        sbpir::{query::Queriable, InternalSignal},
        wit_gen::calc_auto_signals,
    };

    use super::{reduce_degree_mul, SignalFactory};

    #[derive(Default)]
    struct TestSignalFactory {
        counter: u32,
    }

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, _annotation: S) -> Queriable<Fr> {
            self.counter += 1;

            Queriable::Internal(InternalSignal::new(format!("v{}", self.counter)))
        }
    }

    #[test]
    fn test_reduce_degree_mul() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));

        let mut decomp = ConstrDecomp::default();
        let result = reduce_degree_mul(
            &mut decomp,
            vec![a.expr(), b.expr(), c.expr()],
            2,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((b * c) + (-v1))");
        assert_eq!(decomp.constrs.len(), 1);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * c)"));
        assert_eq!(decomp.auto_signals.len(), 1);

        let mut decomp = ConstrDecomp::default();
        let result = reduce_degree_mul(
            &mut decomp,
            vec![(a + b), (b + c), (a + c)],
            2,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "((a + b) * v1)");
        assert_eq!(
            format!("{:#?}", decomp.constrs[0]),
            "(((b + c) * (a + c)) + (-v1))"
        );
        assert_eq!(decomp.constrs.len(), 1);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: ((b + c) * (a + c))"));
        assert_eq!(decomp.auto_signals.len(), 1);
    }

    #[test]
    fn test_reduce_degree() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));

        let (result, decomp) =
            reduce_degree(a * b * c * d * e, 2, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((d * e) + (-v3))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((c * v3) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((b * v2) + (-v1))");
        assert_eq!(decomp.constrs.len(), 3);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v3)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * v2)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (d * e)"));
        assert_eq!(decomp.auto_signals.len(), 3);

        let (result, decomp) = reduce_degree(
            1.expr() - (a * b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(0x1 + (-(a * v1)))");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((d * e) + (-v3))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((c * v3) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((b * v2) + (-v1))");
        assert_eq!(decomp.constrs.len(), 3);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v3)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * v2)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (d * e)"));
        assert_eq!(decomp.auto_signals.len(), 3);

        let (result, decomp) = reduce_degree(
            Pow(Box::new(a.expr()), 4) - (b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "((a * v1) + (-(b * v3)))");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((a * a) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((a * v2) + (-v1))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((d * e) + (-v4))");
        assert_eq!(format!("{:#?}", decomp.constrs[3]), "((c * v4) + (-v3))");
        assert_eq!(decomp.constrs.len(), 4);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (a * a)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (a * v2)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: (d * e)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (c * v4)"));
        assert_eq!(decomp.auto_signals.len(), 4);
    }

    /// Test equality between original expressions and reduced form
    #[test]
    fn test_reduce_degree_eq() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));
        let vars = vec![a, b, c, d, e, f, g];
        let mut assignments = HashMap::new();
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        for v in &vars {
            assignments.insert(*v, Fr::random(&mut rng));
        }

        let expressions = [
            a * b * c * d * e,
            1.expr() - (a * b * c * d * e),
            Pow(Box::new(a.expr()), 4) - (b * c * d * e),
            -(a * b * c * d) * -(a * b * c * d),
            (a - b) * (c - d) * (e - f) * (g - 1),
            (1.expr() - (a - (b * c))) * (1.expr() - (d - (e * f))),
            -(a * -(b * -(c * -d * (-e * -(f * -g))))),
        ];
        let degrees = [2, 3, 4];

        for orig in &expressions {
            let orig_eval = orig.eval(&assignments);
            for degree in &degrees {
                let (result, decomp) =
                    reduce_degree(orig.clone(), *degree, &mut TestSignalFactory::default());
                let mut assignments_result = assignments.clone();
                calc_auto_signals(&decomp.auto_signals, &mut assignments_result);
                let result_eval = result.eval(&assignments_result);
                assert_eq!(
                    result_eval, orig_eval,
                    "reduce degree {} failed on {:#?}",
                    degree, orig
                );

                for constrs in decomp.constrs {
                    let result_eval = constrs.eval(&assignments_result);
                    assert_eq!(
                        result_eval,
                        Some(Fr::ZERO),
                        "reduce degree {} failed on {:#?}",
                        degree,
                        orig
                    );
                }
            }
        }
    }
}
