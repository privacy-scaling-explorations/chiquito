use crate::field::Field;

use super::{ConstrDecomp, Expr, HashResult, SignalFactory};
use std::{fmt::Debug, hash::Hash};

pub fn replace_expr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_se: &Expr<F, V, HashResult>,
    signal_factory: &mut SF,
) -> (Expr<F, V, HashResult>, ConstrDecomp<F, V, HashResult>) {
    let mut decomp = ConstrDecomp::default();

    let new_expr = replace_subexpr(expr, common_se, signal_factory, &mut decomp);
    (new_expr, decomp)
}

fn replace_subexpr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_se: &Expr<F, V, HashResult>,
    signal_factory: &mut SF,
    decomp: &mut ConstrDecomp<F, V, HashResult>,
) -> Expr<F, V, HashResult> {
    let common_expr_hash = common_se.meta().hash;
    // if the expression is the same as the common subexpression, create a new signal and return it
    if expr.meta().hash == common_expr_hash {
        // find the signal or create a new signal for the expression
        let signal = decomp.find_auto_signal_by_hash(common_expr_hash);

        if let Some((s, _)) = signal {
            return Expr::Query(s.clone(), common_se.meta().clone());
        } else {
            let new_var = signal_factory.create(format!("cse_{}", expr.meta().hash));
            decomp.auto_signals.insert(new_var.clone(), expr.clone());
            return Expr::Query(new_var, common_se.meta().clone());
        }   
    }

    expr.apply_subexpressions(|se| replace_subexpr(se, common_se, signal_factory, decomp))
}

#[cfg(test)]
mod tests {
    use std::vec;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{poly::{cse::replace_expr, SignalFactory, ToExpr, VarAssignments}, sbpir::{query::Queriable, InternalSignal}};

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

        let assignments: VarAssignments<Fr, Queriable<Fr>> = vars.iter().cloned().map(|q| (q, Fr::from(2))).collect();

        let (new_expr, decomp) = replace_expr(&expr.hash(&assignments), &common_expr.hash(&assignments), &mut signal_factory);

        assert!(decomp.auto_signals.len() == 1);
        assert_eq!(format!("{:#?}", new_expr), "((-0x1) + cse-1 + (-c))");
    }
}
