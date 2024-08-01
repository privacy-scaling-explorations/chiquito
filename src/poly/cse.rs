use crate::field::Field;

use super::{ConstrDecomp, Expr, HashResult, SignalFactory};
use std::{fmt::Debug, hash::Hash};

/// This function replaces a common subexpression in an expression with a new signal.
pub fn replace_expr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_se: &Expr<F, V, HashResult>,
    signal_factory: &mut SF,
    decomp: ConstrDecomp<F, V, HashResult>,
) -> (Expr<F, V, HashResult>, ConstrDecomp<F, V, HashResult>) {
    let mut decomp = decomp;
    let new_expr = replace_subexpr(expr, common_se, signal_factory, &mut decomp);

    (new_expr, ConstrDecomp::default())
}

/// This function creates a new signal for a common subexpression.
pub fn create_common_ses_signal<
    F: Field,
    V: Clone + PartialEq + Eq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    common_se: &Expr<F, V, HashResult>,
    signal_factory: &mut SF,
) -> (Expr<F, V, HashResult>, ConstrDecomp<F, V, HashResult>) {
    let mut decomp = ConstrDecomp::default();

    let signal = signal_factory.create("cse");
    decomp.auto_eq(signal.clone(), common_se.clone());
    (Expr::Query(signal, common_se.meta().clone()), decomp)
}

/// This function replaces a common subexpression in an expression with a new signal.
fn replace_subexpr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_se: &Expr<F, V, HashResult>,
    signal_factory: &mut SF,
    decomp: &mut ConstrDecomp<F, V, HashResult>,
) -> Expr<F, V, HashResult> {
    let common_expr_hash = common_se.meta().hash;

    if expr.meta().degree < common_se.meta().degree {
        // If the current expression's degree is less than the common subexpression's degree,
        // it can't contain the common subexpression, so we return it as is
        return expr.clone();
    }

    // If the expression is the same as the common subexpression return the signal
    if expr.meta().hash == common_expr_hash {
        return common_se.clone();
    } else {
        // Recursively apply the function to the subexpressions
        expr.apply_subexpressions(|se| replace_subexpr(se, common_se, signal_factory, decomp))
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        poly::{
            cse::{create_common_ses_signal, replace_expr},
            SignalFactory, ToExpr, VarAssignments,
        },
        sbpir::{query::Queriable, InternalSignal},
    };

    #[derive(Default)]
    struct TestSignalFactory {
        counter: u32,
    }

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, _annotation: S) -> Queriable<Fr> {
            self.counter += 1;

            Queriable::Internal(InternalSignal::new(format!("cse-{}", self.counter)))
        }
    }

    #[test]
    fn test_replace_expr() {
        let a = Queriable::Internal(InternalSignal::new("a"));
        let b = Queriable::Internal(InternalSignal::new("b"));
        let c = Queriable::Internal(InternalSignal::new("c"));

        let vars = vec![a.clone(), b.clone(), c.clone()];

        let expr = -1.expr() + a * b - c;
        let common_expr = a * b;

        let mut signal_factory = TestSignalFactory::default();

        let assignments: VarAssignments<Fr, Queriable<Fr>> =
            vars.iter().cloned().map(|q| (q, Fr::from(2))).collect();

        let (common_se, decomp) =
            create_common_ses_signal(&common_expr.hash(&assignments), &mut signal_factory);

        let (new_expr, _) = replace_expr(
            &expr.hash(&assignments),
            &common_se,
            &mut signal_factory,
            decomp.clone(),
        );

        assert!(decomp.auto_signals.len() == 1);
        assert_eq!(format!("{:#?}", new_expr), "((-0x1) + cse-1 + (-c))");
    }
}
