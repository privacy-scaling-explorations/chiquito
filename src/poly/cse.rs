use crate::field::Field;

use super::{ConstrDecomp, Expr, HashResult, SignalFactory};
use std::hash::Hash;

pub fn replace_expr<F: Field + Hash, V: Clone + Eq + Hash>(
    expr: &Expr<F, V, HashResult>,
    common_exprs: &Vec<Expr<F, V, HashResult>>,
    signal_factory: &mut impl SignalFactory<V>,
) -> (Expr<F, V, HashResult>, ConstrDecomp<F, V, HashResult>) {
    let mut decomp = ConstrDecomp::default();
    let new_expr = replace_subexpr(expr, common_exprs, signal_factory, &mut decomp);
    (new_expr, decomp)
}

fn replace_subexpr<F: Field + Hash, V: Clone + Eq + Hash>(
    expr: &Expr<F, V, HashResult>,
    common_exprs: &[Expr<F, V, HashResult>],
    signal_factory: &mut impl SignalFactory<V>,
    decomp: &mut ConstrDecomp<F, V, HashResult>,
) -> Expr<F, V, HashResult> {
    if let Some(_common_expr) = common_exprs
        .iter()
        .find(|ce| ce.meta().hash == expr.meta().hash)
    {
        // Check if there is already a signal for this expression
        if let Some(signal) = decomp
            .auto_signals
            .iter()
            .find(|(_, e)| e.meta().hash == expr.meta().hash)
        {
            return Expr::Query(signal.0.clone(), expr.meta().clone());
        } else {
            let new_var = signal_factory.create(format!("cse_{}", expr.meta().hash));
            decomp.auto_signals.insert(new_var.clone(), expr.clone());
            return Expr::Query(new_var, expr.meta().clone());
        }
    }

    match expr {
        Expr::Sum(ses, m) => Expr::Sum(
            ses.iter()
                .map(|se| replace_subexpr(se, common_exprs, signal_factory, decomp))
                .collect(),
            m.clone(),
        ),
        Expr::Mul(ses, m) => Expr::Mul(
            ses.iter()
                .map(|se| replace_subexpr(se, common_exprs, signal_factory, decomp))
                .collect(),
            m.clone(),
        ),
        Expr::Neg(se, m) => Expr::Neg(
            Box::new(replace_subexpr(se, common_exprs, signal_factory, decomp)),
            m.clone(),
        ),
        Expr::Pow(se, exp, m) => Expr::Pow(
            Box::new(replace_subexpr(se, common_exprs, signal_factory, decomp)),
            *exp,
            m.clone(),
        ),
        Expr::MI(se, m) => Expr::MI(
            Box::new(replace_subexpr(se, common_exprs, signal_factory, decomp)),
            m.clone(),
        ),
        _ => expr.clone(),
    }
}
