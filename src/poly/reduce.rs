use std::{fmt::Debug, hash::Hash};

use crate::{
    field::Field,
    poly::{simplify::simplify_mul, Expr},
};

use super::{ConstrDecomp, SignalFactory};

/// Reduces the degree of an PI by decomposing it in many PI with a maximum degree.
pub fn reduce_degre<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    ctx: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V>,
    max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    reduce_degree_recursive(ctx, constr, max_degree, max_degree, signal_factory)
}

/// Actual recursive implementation of `reduce_degre`. Key here to understand the difference
/// between:  + total_max_degree: maximum degree of the PI the input expression is decomposed of.
///  + partial_max_degree: maximum degree of the root PI, that can substitute the orginal
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
    ctx: &mut ConstrDecomp<F, V>,
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
                        ctx,
                        se,
                        total_max_degree,
                        partial_max_degree,
                        signal_factory,
                    )
                })
                .collect(),
        ),
        Expr::Mul(ses) => reduce_degree_mul(
            ctx,
            ses,
            total_max_degree,
            partial_max_degree,
            signal_factory,
        ),
        Expr::Neg(se) => Expr::Neg(Box::new(reduce_degree_recursive(
            ctx,
            *se,
            total_max_degree,
            partial_max_degree,
            signal_factory,
        ))),
        // TODO: decompose in Pow expressions instead of Mul
        Expr::Pow(se, exp) => reduce_degree_mul(
            ctx,
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
    ctx: &mut ConstrDecomp<F, V>,
    ses: Vec<Expr<F, V>>,
    total_max_degree: usize,
    partial_max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    // base case, if partial_max_degree == 1, the root expresion can only be a variable
    if partial_max_degree == 1 {
        let reduction =
            reduce_degree_mul(ctx, ses, total_max_degree, total_max_degree, signal_factory);
        let signal = signal_factory.create("virtual signal");
        ctx.auto_eq(signal.clone(), reduction);
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
                ctx,
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
    let mut for_root = Vec::new();
    // to_simplify will be multipliers that will be recursively decomposed and subsituted by a
    // virtual signal in the root expression
    let mut to_simplify = Vec::new();

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
    assert!(!to_simplify.is_empty());

    let rest_signal = signal_factory.create("rest_expr");
    for_root.push(Expr::Query(rest_signal.clone()));
    let root_expr = Expr::Mul(for_root);

    // recursion, for the part that exceeds the degree and will be substituted by a virtual signal
    let simplified = reduce_degree_recursive(
        ctx,
        Expr::Mul(to_simplify),
        total_max_degree,
        total_max_degree,
        signal_factory,
    );

    ctx.auto_eq(rest_signal, simplified);

    root_expr
}

#[cfg(test)]
mod test {
    use halo2curves::bn256::Fr;

    use crate::{
        poly::{ConstrDecomp, Expr::*, ToExpr},
        sbpir::{query::Queriable, InternalSignal},
    };

    use super::{reduce_degre, reduce_degree_mul, SignalFactory};

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

        let mut ctx = ConstrDecomp::new();
        let result = reduce_degree_mul(
            &mut ctx,
            vec![a.expr(), b.expr(), c.expr()],
            2,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(format!("{:#?}", ctx.constrs[0]), "((b * c) + (-v1))");
        assert_eq!(ctx.constrs.len(), 1);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * c)"));
        assert_eq!(ctx.auto_signals.len(), 1);

        let mut ctx = ConstrDecomp::new();
        let result = reduce_degree_mul(
            &mut ctx,
            vec![(a + b), (b + c), (a + c)],
            2,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "((a + b) * v1)");
        assert_eq!(
            format!("{:#?}", ctx.constrs[0]),
            "(((b + c) * (a + c)) + (-v1))"
        );
        assert_eq!(ctx.constrs.len(), 1);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: ((b + c) * (a + c))"));
        assert_eq!(ctx.auto_signals.len(), 1);
    }

    #[test]
    fn test_reduce_degree() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));

        let mut ctx = ConstrDecomp::new();
        let result = reduce_degre(
            &mut ctx,
            a * b * c * d * e,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(format!("{:#?}", ctx.constrs[0]), "((d * e) + (-v3))");
        assert_eq!(format!("{:#?}", ctx.constrs[1]), "((c * v3) + (-v2))");
        assert_eq!(format!("{:#?}", ctx.constrs[2]), "((b * v2) + (-v1))");
        assert_eq!(ctx.constrs.len(), 3);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v3)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * v2)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (d * e)"));
        assert_eq!(ctx.auto_signals.len(), 3);

        let mut ctx = ConstrDecomp::new();
        let result = reduce_degre(
            &mut ctx,
            1.expr() - (a * b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(0x1 + (-(a * v1)))");
        assert_eq!(format!("{:#?}", ctx.constrs[0]), "((d * e) + (-v3))");
        assert_eq!(format!("{:#?}", ctx.constrs[1]), "((c * v3) + (-v2))");
        assert_eq!(format!("{:#?}", ctx.constrs[2]), "((b * v2) + (-v1))");
        assert_eq!(ctx.constrs.len(), 3);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v3)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (b * v2)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (d * e)"));
        assert_eq!(ctx.auto_signals.len(), 3);

        let mut ctx = ConstrDecomp::new();
        let result = reduce_degre(
            &mut ctx,
            Pow(Box::new(a.expr()), 4) - (b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "((a * v1) + (-(b * v3)))");
        assert_eq!(format!("{:#?}", ctx.constrs[0]), "((a * a) + (-v2))");
        assert_eq!(format!("{:#?}", ctx.constrs[1]), "((a * v2) + (-v1))");
        assert_eq!(format!("{:#?}", ctx.constrs[2]), "((d * e) + (-v4))");
        assert_eq!(format!("{:#?}", ctx.constrs[3]), "((c * v4) + (-v3))");
        assert_eq!(ctx.constrs.len(), 4);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (a * a)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (a * v2)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: (d * e)"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (c * v4)"));
        assert_eq!(ctx.auto_signals.len(), 4);
    }
}
