use crate::field::Field;

use super::{ConstrDecomp, Expr, HashResult, SignalFactory};
use std::{hash::Hash, fmt::Debug};

pub fn replace_expr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_exprs: &[Expr<F, V, HashResult>],
    signal_factory: &mut SF,
) -> (Expr<F, V, HashResult>, ConstrDecomp<F, V, HashResult>) {
    let mut decomp = ConstrDecomp::default();
    let new_expr = replace_subexpr(expr, common_exprs, signal_factory, &mut decomp);
    (new_expr, decomp)
}

fn replace_subexpr<F: Field + Hash, V: Clone + Eq + Hash + Debug, SF: SignalFactory<V>>(
    expr: &Expr<F, V, HashResult>,
    common_exprs: &[Expr<F, V, HashResult>],
    signal_factory: &mut SF,
    decomp: &mut ConstrDecomp<F, V, HashResult>,
) -> Expr<F, V, HashResult> {
    if let Some(_common_expr) = common_exprs
        .iter()
        .find(|ce| ce.meta().hash == expr.meta().hash)
    {
        // Check if there is already a signal for this expression
        if let Some(signal) = decomp.find_auto_signal_by_hash(expr.meta().hash) {
            return Expr::Query(signal.0.clone(), expr.meta().clone());
        } else {
            let new_var = signal_factory.create(format!("cse_{}", expr.meta().hash));
            decomp.auto_signals.insert(new_var.clone(), expr.clone());
            return Expr::Query(new_var, expr.meta().clone());
        }
    }

    expr.apply_subexpressions(|se| replace_subexpr(se, common_exprs, signal_factory, decomp))
}
