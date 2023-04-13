use halo2_proofs::halo2curves::FieldExt;

use crate::ast::{Expr, ToExpr};

pub fn and<F: From<u64>, E: Into<Expr<F>>, I: IntoIterator<Item = E>>(inputs: I) -> Expr<F> {
    inputs
        .into_iter()
        .fold(1u64.expr(), |acc, input| acc * input.into())
}

pub fn or<F: From<u64>, E: Into<Expr<F>>, I: IntoIterator<Item = E>>(inputs: I) -> Expr<F> {
    not(and(inputs.into_iter().map(not)))
}

pub fn xor<F: From<u64> + Clone, LHS: Into<Expr<F>>, RHS: Into<Expr<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Expr<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    lhs.clone() + rhs.clone() - 2u64.expr() * lhs * rhs
}

pub fn eq<F, LHS: Into<Expr<F>>, RHS: Into<Expr<F>>>(lhs: LHS, rhs: RHS) -> Expr<F> {
    lhs.into() - rhs.into()
}

pub fn select<F: From<u64>, T1: Into<Expr<F>> + Clone, T2: Into<Expr<F>>, T3: Into<Expr<F>>>(
    selector: T1,
    when_true: T2,
    when_false: T3,
) -> Expr<F> {
    selector.clone().into() * when_true.into() + (1u64.expr() - selector.into()) * when_false
}

// not, works only if the parameter is 0 or 1
pub fn not<F: From<u64>, T: Into<Expr<F>>>(expr: T) -> Expr<F> {
    1u64.expr() - expr.into()
}

/// Is zero
pub fn isz<F, T: Into<Expr<F>>>(expr: T) -> Expr<F> {
    expr.into()
}

pub fn rlc<F: FieldExt, E: Into<Expr<F>> + Clone, R: Into<Expr<F>> + Clone>(
    exprs: &[E],
    randomness: R,
) -> Expr<F> {
    if !exprs.is_empty() {
        let mut exprs = exprs.iter().rev().map(|e| e.clone().into());
        let init = exprs.next().expect("should not be empty");

        exprs.fold(init, |acc, expr| acc * randomness.clone().into() + expr)
    } else {
        0i32.expr()
    }
}
