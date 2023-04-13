use std::{fmt::Debug, vec};

use crate::ast::{query::Queriable, Expr, ToExpr};

#[derive(Clone)]
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
}

impl<F: Debug> From<Expr<F>> for Constraint<F> {
    fn from(expr: Expr<F>) -> Self {
        let annotation = format!("{:?}", &expr);
        Self { expr, annotation }
    }
}

impl<F> From<Queriable<F>> for Constraint<F> {
    fn from(query: Queriable<F>) -> Self {
        annotate(query.annotation(), Expr::Query(query))
    }
}

impl<F> Debug for Constraint<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.annotation)
    }
}

pub fn and<F: From<u64>, E: Into<Constraint<F>>, I: IntoIterator<Item = E>>(
    inputs: I,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];
    let mut expr: Expr<F> = 1u64.expr();

    for constraint in inputs.into_iter() {
        let constraint = constraint.into();
        annotations.push(constraint.annotation);

        expr = expr * constraint.expr;
    }

    Constraint {
        annotation: format!("({})", annotations.join(" AND ")),
        expr,
    }
}

pub fn or<
    F: From<u64> + Debug,
    E: Into<Constraint<F>> + Clone,
    I: IntoIterator<Item = E> + Clone,
>(
    inputs: I,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];
    let mut exprs: Vec<Expr<F>> = vec![];

    for constraint in inputs.into_iter() {
        let constraint = constraint.into();
        annotations.push(constraint.annotation);
        exprs.push(constraint.expr);
    }

    let result = not(and(exprs.into_iter().map(not)));

    Constraint {
        annotation: format!("({})", annotations.join(" OR ")),
        expr: result.expr,
    }
}

pub fn xor<F: From<u64> + Clone, LHS: Into<Expr<F>>, RHS: Into<Expr<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Expr<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    lhs.clone() + rhs.clone() - 2u64.expr() * lhs * rhs
}

pub fn eq<F, LHS: Into<Constraint<F>>, RHS: Into<Constraint<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Constraint<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    Constraint {
        annotation: format!("{} == {}", lhs.annotation, rhs.annotation),
        expr: lhs.expr - rhs.expr,
    }
}

pub fn select<
    F: From<u64> + Clone,
    T1: Into<Constraint<F>>,
    T2: Into<Constraint<F>>,
    T3: Into<Constraint<F>>,
>(
    selector: T1,
    when_true: T2,
    when_false: T3,
) -> Constraint<F> {
    let selector = selector.into();
    let when_true = when_true.into();
    let when_false = when_false.into();

    Constraint {
        annotation: format!(
            "if({})then({})else({})",
            selector.annotation, when_true.annotation, when_false.annotation
        ),
        expr: selector.expr.clone() * when_true.expr
            + (1u64.expr() - selector.expr) * when_false.expr,
    }
}

// not, works only if the parameter is 0 or 1
pub fn not<F: From<u64>, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();
    let annotation = format!("NOT({})", constraint.annotation);
    let expr = 1u64.expr() - constraint.expr;

    Constraint { annotation, expr }
}

/// Is zero
pub fn isz<F, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();

    Constraint {
        annotation: format!("0 == {}", constraint.annotation),
        expr: constraint.expr,
    }
}

pub fn annotate<F, E: Into<Expr<F>>>(annotation: String, expr: E) -> Constraint<F> {
    Constraint {
        annotation,
        expr: expr.into(),
    }
}

pub fn rlc<F: From<u64>, E: Into<Expr<F>> + Clone, R: Into<Expr<F>> + Clone>(
    exprs: &[E],
    randomness: R,
) -> Expr<F> {
    if !exprs.is_empty() {
        let mut exprs = exprs.iter().rev().map(|e| e.clone().into());
        let init = exprs.next().expect("should not be empty");

        exprs.fold(init, |acc, expr| acc * randomness.clone().into() + expr)
    } else {
        0u64.expr()
    }
}
