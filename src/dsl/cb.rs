use std::{fmt::Debug, vec};

use halo2_proofs::arithmetic::Field;

use crate::ast::{query::Queriable, Expr, ToExpr};

use super::{
    lb::{InPlaceLookupBuilder, LookupTableStore},
    StepTypeHandler,
};

/// Represents a constraint with an associated annotation and expression.
#[derive(Clone)]
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
    pub typing: Typing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Typing {
    Unknown,
    Boolean,
    AntiBooly,
}

impl<F: Debug> From<Expr<F>> for Constraint<F> {
    fn from(expr: Expr<F>) -> Self {
        let annotation = format!("{:?}", &expr);
        match expr {
            Expr::Query(Queriable::StepTypeNext(_)) => Self {
                expr,
                annotation,
                typing: Typing::Boolean,
            },
            _ => Self {
                expr,
                annotation,
                typing: Typing::Unknown,
            },
        }
    }
}

impl<F> From<Queriable<F>> for Constraint<F> {
    fn from(query: Queriable<F>) -> Self {
        match query {
            Queriable::StepTypeNext(_) => {
                annotate(query.annotation(), Expr::Query(query), Typing::Boolean)
            }
            _ => annotate(query.annotation(), Expr::Query(query), Typing::Unknown),
        }
    }
}

impl<F: Field + From<u64> + Debug> From<i32> for Constraint<F> {
    fn from(v: i32) -> Self {
        v.expr().into()
    }
}

macro_rules! impl_cb_like {
    ($type:ty) => {
        impl<F: From<u64> + Debug> From<$type> for Constraint<F> {
            #[inline]
            fn from(value: $type) -> Self {
                Expr::Const(F::from(value as u64)).into()
            }
        }
    };
}

impl_cb_like!(bool);
impl_cb_like!(u8);
impl_cb_like!(u32);
impl_cb_like!(u64);
impl_cb_like!(usize);

impl<F> Debug for Constraint<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.annotation)
    }
}

/// Takes an iterator of input constraints and returns a new constraint representing the logical AND
/// of all input constraints. In practice, multiplies all input constraints together, i.e. A * B * C
/// * … = 0.
pub fn and<F: From<u64>, E: Into<Constraint<F>>, I: IntoIterator<Item = E>>(
    inputs: I,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];
    let mut expr: Expr<F> = 1u64.expr();

    for constraint in inputs.into_iter() {
        let constraint = constraint.into();
        match constraint.typing {
            Typing::Boolean | Typing::Unknown => {
                annotations.push(constraint.annotation);
                expr = expr * constraint.expr;
            }
            Typing::AntiBooly => panic!(
                "Expected Boolean or Unknown constraint, got AntiBooly (constraint: {})",
                constraint.annotation
            ),
        }
    }

    Constraint {
        annotation: format!("({})", annotations.join(" AND ")),
        expr,
        typing: Typing::Boolean,
    }
}

/// Takes an iterator of input constraints and returns a new constraint representing the logical OR
/// of all input constraints. In practice, constructs the output constraint in the format of
/// not(and(not(A), not(B), not(C), …)) = 0, which is equivalent to or(A, B, C, …).
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
        match constraint.typing {
            Typing::Boolean | Typing::Unknown => {
                annotations.push(constraint.annotation);
                exprs.push(constraint.expr);
            }
            Typing::AntiBooly => panic!(
                "Expected Boolean or Unknown constraint, got AntiBooly (constraint: {})",
                constraint.annotation
            ),
        }
    }

    let result = not(and(exprs.into_iter().map(not)));

    Constraint {
        annotation: format!("({})", annotations.join(" OR ")),
        expr: result.expr,
        typing: Typing::Boolean,
    }
}

/// Takes two expressions and returns a new expression representing the logical XOR of the input
/// expressions.
pub fn xor<F: From<u64> + Clone, LHS: Into<Constraint<F>>, RHS: Into<Constraint<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];

    let lhs: Constraint<F> = lhs.into();
    let rhs: Constraint<F> = rhs.into();

    let expr = match (lhs.typing, rhs.typing) {
        (Typing::Boolean | Typing::Unknown, Typing::Boolean | Typing::Unknown) => {
            annotations.push(lhs.annotation);
            annotations.push(rhs.annotation);
            lhs.expr.clone() + rhs.expr.clone() - 2u64.expr() * lhs.expr * rhs.expr
        },
        _ => panic!("Expected Boolean or Unknown constraints, got AntiBooly in one of lhs or rhs constraints (lhs constraint: {}) (rhs constraint: {})", lhs.annotation, rhs.annotation),
    };

    Constraint {
        annotation: format!("({})", annotations.join(" XOR ")),
        expr,
        typing: Typing::Boolean,
    }
}

/// Takes two constraints and returns a new constraint representing the equality of the input
/// constraints.
pub fn eq<F, LHS: Into<Constraint<F>>, RHS: Into<Constraint<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Constraint<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    Constraint {
        annotation: format!("{} == {}", lhs.annotation, rhs.annotation),
        expr: lhs.expr - rhs.expr,
        typing: Typing::AntiBooly,
    }
}

/// Takes a selector constraint and two other constraints, and returns a new constraint that
/// represents the value of `when_true` if the selector is true, or `when_false` if the selector is
/// false.
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

    if selector.typing == Typing::AntiBooly {
        panic!(
            "Expected Boolean or Unknown selector, got AntiBooly (selector: {})",
            selector.annotation
        )
    }

    let typing = if when_true.typing == when_false.typing {
        when_true.typing
    } else {
        Typing::Unknown
    };

    Constraint {
        annotation: format!(
            "if({})then({})else({})",
            selector.annotation, when_true.annotation, when_false.annotation
        ),
        expr: selector.expr.clone() * when_true.expr
            + (1u64.expr() - selector.expr) * when_false.expr,
        typing,
    }
}

/// Takes a selector constraint and a `when_true` constraint, and returns a new constraint that
/// represents the value of `when_true` if the selector is true, or zero if the selector is false.
pub fn when<F: From<u64> + Clone, T1: Into<Constraint<F>>, T2: Into<Constraint<F>>>(
    selector: T1,
    when_true: T2,
) -> Constraint<F> {
    let selector = selector.into();
    let when_true = when_true.into();

    if selector.typing == Typing::AntiBooly {
        panic!(
            "Expected Boolean or Unknown selector, got AntiBooly (selector: {})",
            selector.annotation
        )
    }

    Constraint {
        annotation: format!("if({})then({})", selector.annotation, when_true.annotation),
        expr: selector.expr * when_true.expr,
        typing: when_true.typing,
    }
}

/// Takes a selector constraint and a `when_false` constraint, and returns a new constraint that
/// represents the value of `when_false` unless the selector is true, in which case it returns zero.
pub fn unless<F: From<u64> + Clone, T1: Into<Constraint<F>>, T2: Into<Constraint<F>>>(
    selector: T1,
    when_false: T2,
) -> Constraint<F> {
    let selector = selector.into();
    let when_false = when_false.into();

    if selector.typing == Typing::AntiBooly {
        panic!(
            "Expected Boolean or Unknown selector, got AntiBooly (selector: {})",
            selector.annotation
        )
    }

    Constraint {
        annotation: format!(
            "unless({})then({})",
            selector.annotation, when_false.annotation
        ),
        expr: (1u64.expr() - selector.expr) * when_false.expr,
        typing: when_false.typing,
    }
}

/// Takes a constraint and returns a new constraint representing the logical NOT of the input
/// constraint. The input constraint must have a value of either 0 or 1.
pub fn not<F: From<u64>, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();
    if constraint.typing == Typing::AntiBooly {
        panic!(
            "Expected Boolean or Unknown constraint, got AntiBooly (constraint: {})",
            constraint.annotation
        );
    }
    let annotation = format!("NOT({})", constraint.annotation);
    let expr = 1u64.expr() - constraint.expr;

    Constraint {
        annotation,
        expr,
        typing: Typing::Boolean,
    }
}

/// Takes a constraint and returns a new constraint representing whether the input constraint is
/// zero.
pub fn isz<F, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();

    Constraint {
        annotation: format!("0 == {}", constraint.annotation),
        expr: constraint.expr,
        typing: Typing::AntiBooly,
    }
}

/// Takes a `StepTypeHandler` and a constraint, and returns a new constraint that is only applied if
/// the next step is of the given step type.
pub fn if_next_step<F: Clone, T: Into<Constraint<F>>, ST: Into<StepTypeHandler>>(
    step_type: ST,
    constraint: T,
) -> Constraint<F> {
    let constraint = constraint.into();
    let step_type = step_type.into();

    let annotation = format!(
        "if(next step is {})then({})",
        step_type.annotation, constraint.annotation
    );

    Constraint {
        expr: step_type.next() * constraint.expr,
        annotation,
        typing: constraint.typing,
    }
}

/// Takes a `StepTypeHandler` and returns a new constraint that requires the next step to be of the
/// given step type.
pub fn next_step_must_be<F: From<u64>, ST: Into<StepTypeHandler>>(step_type: ST) -> Constraint<F> {
    let step_type = step_type.into();

    annotate(
        format!("next_step_must_be({})", step_type.annotation),
        not(step_type.next()),
        Typing::AntiBooly,
    )
}

/// Takes a `StepTypeHandler` and returns a new constraint that requires the next step to not be of
/// the given step type.
pub fn next_step_must_not_be<F: From<u64>, ST: Into<StepTypeHandler>>(
    step_type: ST,
) -> Constraint<F> {
    let step_type = step_type.into();

    annotate(
        format!("next_step_must_not_be({})", step_type.annotation),
        step_type.next(),
        Typing::AntiBooly,
    )
}

/// Takes a string annotation and an expression, and returns a new constraint with the given
/// annotation and expression.
pub fn annotate<F, E: Into<Expr<F>>>(annotation: String, expr: E, typing: Typing) -> Constraint<F> {
    Constraint {
        annotation,
        expr: expr.into(),
        typing,
    }
}

/// Computes the randomized linear combination of the given expressions and randomness.
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

/// Creates a new empty `LookupBuilder` object and returns it. Can an chain multiple `add` and
/// `enable` function calls after to build the lookup table.
pub fn lookup<F: Debug + Clone>() -> InPlaceLookupBuilder<F> {
    InPlaceLookupBuilder::default()
}

pub fn table<F: Default>() -> LookupTableStore<F> {
    LookupTableStore::default()
}

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;

    use super::*;
    use crate::ast::{ToExpr, ToField};

    #[test]
    fn test_and_empty() {
        let inputs: Vec<Constraint<Fr>> = vec![];
        let result = and(inputs);
        assert_eq!(result.annotation, "()");
        assert!(matches!(result.expr, Expr::Const(c) if c == 1u64.field()));
    }

    #[test]
    fn test_and_single_input() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let result = and(vec![a]);

        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field())));
    }

    #[test]
    fn test_and_multiple_inputs() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let b = 20.expr();
        let c = 30.expr();
        let result = and(vec![a, b, c]);

        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 4 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field()) &&
            matches!(v[2], Expr::Const(c) if c == 20u64.field()) &&
            matches!(v[3], Expr::Const(c) if c == 30u64.field())));
    }

    #[test]
    fn test_or_empty() {
        let inputs: Vec<Constraint<Fr>> = vec![];
        let result = or(inputs);

        // returns "1 - 1", because `and` with empty input defaults to 1, and `not` returns "1 -
        // expr"
        assert_eq!(result.annotation, "()");
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
        matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
        matches!(&v[1], Expr::Neg(boxed_e) if
            matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 1u64.field()))));
    }

    #[test]
    fn test_or_single_input() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let result = or(vec![a]);

        // returns "1 - (1 * (1 - 10))"
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(&v[1], Expr::Neg(mul) if
                matches!(mul.as_ref(), Expr::Mul(v) if v.len() == 2 &&
                    matches!(v[0], Expr::Const(c) if c == 1u64.field()) && 
                    matches!(&v[1], Expr::Sum(v) if v.len() == 2 &&
                        matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                        matches!(&v[1], Expr::Neg(boxed_e) if
                            matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 10u64.field())))))));
    }

    #[test]
    fn test_or_multiple_input() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let b = <u64 as ToExpr<Fr>>::expr(&20);
        let c = <u64 as ToExpr<Fr>>::expr(&30);
        let result = or(vec![a, b, c]);

        // returns "1 - (1 * (1 - 10) * (1 - 20) * (1 - 30))"
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(&v[1], Expr::Neg(boxed_mul) if
                matches!(boxed_mul.as_ref(), Expr::Mul(v) if v.len() == 4 &&
                    matches!(v[0], Expr::Const(c) if c == 1u64.field()) && 
                    matches!(&v[1], Expr::Sum(v) if v.len() == 2 &&
                        matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                        matches!(&v[1], Expr::Neg(boxed_e) if 
                            matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 10u64.field()))) &&
                    matches!(&v[2], Expr::Sum(v) if v.len() == 2 &&
                        matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                        matches!(&v[1], Expr::Neg(boxed_e) if 
                            matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 20u64.field()))) &&
                    matches!(&v[3], Expr::Sum(v) if v.len() == 2 &&
                        matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                        matches!(&v[1], Expr::Neg(boxed_e) if 
                            matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 30u64.field())))))));
    }

    #[test]
    fn test_not_one() {
        let a = <u64 as ToExpr<Fr>>::expr(&1);
        let result = not(a);

        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(&v[1], Expr::Neg(boxed_e) if
                matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 1u64.field()))));
    }

    #[test]
    fn test_not_zero() {
        let a = <u64 as ToExpr<Fr>>::expr(&0);
        let result = not(a);

        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(&v[1], Expr::Neg(boxed_e) if
                matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 0u64.field()))));
    }

    #[test]
    fn test_xor() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let b = <u64 as ToExpr<Fr>>::expr(&20);
        let result = xor(a, b);

        // returns "10 + 20 - 2 * 10 * 20"
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 3 &&
            matches!(v[0], Expr::Const(c) if c == 10u64.field()) &&
            matches!(v[1], Expr::Const(c) if c == 20u64.field()) &&
            matches!(&v[2], Expr::Neg(boxed_mul) if
                matches!(boxed_mul.as_ref(), Expr::Mul(v) if v.len() == 3 &&
                    matches!(v[0], Expr::Const(c) if c == 2u64.field()) &&
                    matches!(v[1], Expr::Const(c) if c == 10u64.field()) &&
                    matches!(v[2], Expr::Const(c) if c == 20u64.field())))));
    }

    #[test]
    fn test_eq() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let b = <u64 as ToExpr<Fr>>::expr(&20);
        let result = eq(a, b);

        // returns "10 - 20"
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 10u64.field()) &&
            matches!(&v[1], Expr::Neg(boxed_e) if
                matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 20u64.field()))));
    }

    #[test]
    fn test_select() {
        let selector = <u64 as ToExpr<Fr>>::expr(&1);
        let when_true = <u64 as ToExpr<Fr>>::expr(&10);
        let when_false = <u64 as ToExpr<Fr>>::expr(&20);
        let result = select(selector, when_true, when_false);

        // returns "1 * 10 + (1 - 1) * 20"
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
            matches!(&v[0], Expr::Mul(v) if v.len() == 2 &&
                matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                matches!(v[1], Expr::Const(c) if c == 10u64.field())) &&
            matches!(&v[1], Expr::Mul(v) if v.len() == 2 &&
                matches!(&v[0], Expr::Sum(v) if v.len() == 2 &&
                    matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                    matches!(&v[1], Expr::Neg(boxed_e) if
                        matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 1u64.field()))) &&
                matches!(v[1], Expr::Const(c) if c == 20u64.field()))));
    }

    #[test]
    fn test_when_true() {
        let selector = <u64 as ToExpr<Fr>>::expr(&1);
        let when_true = <u64 as ToExpr<Fr>>::expr(&10);
        let result = when(selector, when_true);

        // returns "1 * 10"
        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field())));
    }

    #[test]
    fn test_when_false() {
        let selector = <u64 as ToExpr<Fr>>::expr(&0);
        let when_true = <u64 as ToExpr<Fr>>::expr(&10);
        let result = when(selector, when_true);

        // returns "0 * 10"
        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 2 &&
            matches!(v[0], Expr::Const(c) if c == 0u64.field()) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field())));
    }

    #[test]
    fn test_unless() {
        let selector = <u64 as ToExpr<Fr>>::expr(&1);
        let when_false = <u64 as ToExpr<Fr>>::expr(&10);
        let result = unless(selector, when_false);

        // returns "(1 - 1) * 10"
        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 2 &&
            matches!(&v[0], Expr::Sum(v) if v.len() == 2 &&
                matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                matches!(&v[1], Expr::Neg(boxed_e) if
                    matches!(boxed_e.as_ref(), Expr::Const(c) if *c == 1u64.field()))) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field())));
    }

    #[test]
    fn test_isz() {
        let zero = <u64 as ToExpr<Fr>>::expr(&0);
        let non_zero = <u64 as ToExpr<Fr>>::expr(&10);
        let result_zero = isz(zero);
        let result_non_zero = isz(non_zero);

        // returns "0"
        assert!(matches!(result_zero.expr, Expr::Const(c) if c == 0u64.field()));
        // returns "10"
        assert!(matches!(result_non_zero.expr, Expr::Const(c) if c == 10u64.field()));
    }

    #[test]
    fn test_if_next_step() {
        let step_type = StepTypeHandler::new("test_step".to_string());
        let constraint = <u64 as ToExpr<Fr>>::expr(&10);
        let result = if_next_step(step_type, constraint);

        // returns "Expr::Query(Queriable::StepTypeNext(StepTypeHandler{id: _id, annotation:
        // annotation})) * 10"
        assert!(matches!(result.expr, Expr::Mul(v) if v.len() == 2 &&
                    matches!(v[0], Expr::Query(Queriable::StepTypeNext(s)) if
                        matches!(s, StepTypeHandler {id: _id, annotation: "test_step"})) &&
                    matches!(v[1], Expr::Const(c) if c == 10u64.field())
        ));
    }

    #[test]
    fn test_next_step_must_be() {
        let step_type = StepTypeHandler::new("test_step".to_owned());
        let result: Constraint<Fr> = next_step_must_be(step_type);

        // returns "1 - Expr::Query(Queriable::StepTypeNext(StepTypeHandler{id: _id, annotation:
        // annotation}))"
        assert_eq!(result.annotation, "next_step_must_be(test_step)");
        assert!(matches!(result.expr, Expr::Sum(v) if v.len() == 2 &&
                    matches!(v[0], Expr::Const(c) if c == 1u64.field()) &&
                    matches!(&v[1], Expr::Neg(boxed_e) if
                        matches!(boxed_e.as_ref(), Expr::Query(Queriable::StepTypeNext(s)) if
                            matches!(s, StepTypeHandler {id: _id, annotation: "test_step"})))));
    }

    #[test]
    fn test_next_step_must_not_be() {
        let step_type = StepTypeHandler::new("test_step".to_owned());
        let result: Constraint<Fr> = next_step_must_not_be(step_type);

        // returns "Expr::Query(Queriable::StepTypeNext(StepTypeHandler{id: _id, annotation:
        // annotation}))"
        assert_eq!(result.annotation, "next_step_must_not_be(test_step)");
        assert!(
            matches!(result.expr, Expr::Query(Queriable::StepTypeNext(s)) if
                        matches!(s, StepTypeHandler {id: _id, annotation: "test_step"}))
        );
    }

    #[test]
    fn test_annotate() {
        let expr = <u64 as ToExpr<Fr>>::expr(&10);
        let result = annotate("my_constraint".to_string(), expr, Typing::Unknown);

        assert_eq!(result.annotation, "my_constraint");
        assert!(matches!(result.expr, Expr::Const(c) if c == 10u64.field()));
        assert!(matches!(result.typing, Typing::Unknown));
    }

    #[test]
    fn test_rlc_empty() {
        let randomness = <u64 as ToExpr<Fr>>::expr(&40);
        let result = rlc::<Fr, Expr<Fr>, Expr<Fr>>(&[], randomness);

        // returns "0"
        assert!(matches!(result, Expr::Const(c) if c == 0u64.field()));
    }

    #[test]
    fn test_rlc_one_input() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let result = rlc(&[a], 40u64.expr());

        // returns "10"
        assert!(matches!(result, Expr::Const(c) if c == 10u64.field()));
    }

    #[test]
    fn test_rlc_multiple_inputs() {
        let a = <u64 as ToExpr<Fr>>::expr(&10);
        let b = 20u64.expr();
        let c = 30u64.expr();
        let result = rlc(&[a, b, c], 40u64.expr());

        // returns "(30 * 40 + 20) * 40 + 10"
        assert!(matches!(result, Expr::Sum(v) if v.len() == 2 &&
            matches!(&v[0], Expr::Mul(v) if v.len() == 2 &&
                matches!(&v[0], Expr::Sum(v) if
                    matches!(&v[0], Expr::Mul(v) if v.len() == 2 &&
                        matches!(v[0], Expr::Const(c) if c == 30u64.field()) &&
                        matches!(v[1], Expr::Const(c) if c == 40u64.field())) &&
                    matches!(v[1], Expr::Const(c) if c == 20u64.field())) &&
                matches!(v[1], Expr::Const(c) if c == 40u64.field())) &&
            matches!(v[1], Expr::Const(c) if c == 10u64.field())));
    }
}
