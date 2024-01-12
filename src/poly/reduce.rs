use std::{fmt::Debug, hash::Hash};

use crate::{
    field::Field,
    poly::{simplify::simplify_mul, Expr},
};

use super::{ConstrDecomp, SignalFactory};

/// Actual recursive implementation of `reduce_degree`. Key here to understand the difference
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
fn reduce_degree<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V>,
    max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    if constr.degree() <= max_degree {
        return constr;
    }

    match constr {
        Expr::Const(_) => constr,
        Expr::Sum(ses) => Expr::Sum(
            ses.into_iter()
                .map(|se| reduce_degree(decomp, se, max_degree, signal_factory))
                .collect(),
        ),
        Expr::Mul(ses) => reduce_degree_mul(decomp, ses, max_degree, signal_factory),
        Expr::Neg(se) => Expr::Neg(Box::new(reduce_degree(
            decomp,
            *se,
            max_degree,
            signal_factory,
        ))),
        // TODO: decompose in Pow expressions instead of Mul
        Expr::Pow(se, exp) => reduce_degree_mul(
            decomp,
            std::vec::from_elem(*se, exp as usize),
            max_degree,
            signal_factory,
        ),
        Expr::Query(_) => constr,
        Expr::Halo2Expr(_) => unimplemented!(),
        Expr::MI(_) => unimplemented!(),
    }
}
fn reduce_degree_mul<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    decomp: &mut ConstrDecomp<F, V>,
    mut ses: Vec<Expr<F, V>>,
    max_degree: usize,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    assert!(max_degree > 1);
    let mut tail = Vec::new();
    // Remove multiplicands until ses is degree `max_degree-1`.
    while ses.iter().map(|se| se.degree()).sum::<usize>() > max_degree - 1 {
        tail.push(ses.pop().expect("ses.len() > 0"));
    }
    if tail.len() == 0 {
        // Input expression is below max_degree
        Expr::Mul(ses)
    } else if tail.len() == 1 && ses.len() == 0 {
        // Input expression contains a single multiplicand with degree > 1, unwrap it and recurse.
        reduce_degree(
            decomp,
            tail.pop().expect("tail.len() == 1"),
            max_degree,
            signal_factory,
        )
    } else {
        // Only one multiplicand in the tail and it's already degree 1, so no reduction needed.
        if tail.len() == 1 && tail[0].degree() == 1 {
            ses.push(tail.pop().expect("tail.len() == 1"));
            return Expr::Mul(ses);
        }
        // Reverse the tail to keep the original expression order
        tail.reverse();
        let reduction = reduce_degree_mul(decomp, tail, max_degree, signal_factory);
        let signal = signal_factory.create("virtual signal");
        decomp.auto_eq(signal.clone(), reduction);
        ses.push(Expr::Query(signal));
        Expr::Mul(ses)
    }
}

#[cfg(test)]
mod test {
    use halo2curves::bn256::Fr;

    use crate::{
        poly::{ConstrDecomp, Expr::*, ToExpr},
        sbpir::{query::Queriable, InternalSignal},
    };

    use super::{reduce_degree, reduce_degree_mul, SignalFactory};

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

        let mut decomp = ConstrDecomp::new();
        let result = reduce_degree_mul(
            &mut decomp,
            vec![a.expr(), b.expr(), c.expr()],
            2,
            // 2,
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

        let mut decomp = ConstrDecomp::new();
        let result = reduce_degree_mul(
            &mut decomp,
            vec![(a + b), (b + c), (a + c)],
            2,
            // 2,
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
    fn test_reduce_degree_all() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));

        let mut decomp = ConstrDecomp::new();
        let result = reduce_degree(
            &mut decomp,
            a * b * c * d * e,
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(a * v3)");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((d * e) + (-v1))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((c * v1) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((b * v2) + (-v3))");
        assert_eq!(decomp.constrs.len(), 3);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v1)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (b * v2)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (d * e)"));
        assert_eq!(decomp.auto_signals.len(), 3);

        let mut decomp = ConstrDecomp::new();
        let result = reduce_degree(
            &mut decomp,
            1.expr() - (a * b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "(0x1 + (-(a * v3)))");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((d * e) + (-v1))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((c * v1) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((b * v2) + (-v3))");
        assert_eq!(decomp.constrs.len(), 3);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (d * e)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (c * v1)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (b * v2)"));
        assert_eq!(decomp.auto_signals.len(), 3);

        let mut decomp = ConstrDecomp::new();
        let result = reduce_degree(
            &mut decomp,
            Pow(Box::new(a.expr()), 4) - (b * c * d * e),
            2,
            &mut TestSignalFactory::default(),
        );

        assert_eq!(format!("{:#?}", result), "((a * v2) + (-(b * v4)))");
        assert_eq!(format!("{:#?}", decomp.constrs[0]), "((a * a) + (-v1))");
        assert_eq!(format!("{:#?}", decomp.constrs[1]), "((a * v1) + (-v2))");
        assert_eq!(format!("{:#?}", decomp.constrs[2]), "((d * e) + (-v3))");
        assert_eq!(format!("{:#?}", decomp.constrs[3]), "((c * v3) + (-v4))");
        assert_eq!(decomp.constrs.len(), 4);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: (a * a)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: (a * v1)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: (d * e)"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: (c * v3)"));
        assert_eq!(decomp.auto_signals.len(), 4);
    }
}
