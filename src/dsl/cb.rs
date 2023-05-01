use std::{fmt::Debug, vec};

use halo2_proofs::arithmetic::Field;

use crate::ast::{query::Queriable, Expr, Lookup, ToExpr};

use super::StepTypeHandler;

/// The **`Constraint`** struct represents a constraint with an associated annotation and expression.
#[derive(Clone)]
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
}

/// **`Constraint<F>`** can be converted from `Expr<F>`.
impl<F: Debug> From<Expr<F>> for Constraint<F> {    
    fn from(expr: Expr<F>) -> Self {
        let annotation = format!("{:?}", &expr);
        Self { expr, annotation }
    }
}

/// **`Constraint<F>`** can be converted from `Queriable<F>`.
impl<F> From<Queriable<F>> for Constraint<F> {
    fn from(query: Queriable<F>) -> Self {
        annotate(query.annotation(), Expr::Query(query))
    }
}

/// **`Constraint<F>`** can be converted from `i32`.
impl<F: Field + From<u64> + Debug> From<i32> for Constraint<F> {
    fn from(v: i32) -> Self {
        v.expr().into()
    }
}

/// **`Constraint<F>`** can be converted from `bool`, `u8`, `u32`, `u64`, and `usize`.
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

/// The **`and`** function takes an iterator of input constraints and returns a new constraint representing the logical AND of all input constraints. In practice, multiplies all input constraints together, i.e. A * B * C * … = 0.
/// # **Arguments:**
/// - **`inputs`**: An iterator of items that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the logical AND of all input constraints.
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

/// The **`or`** function takes an iterator of input constraints and returns a new constraint representing the logical OR of all input constraints. In practice, constructs the output constraint in the format of not(and(not(A), not(B), not(C), …)) = 0, which is equivalent to or(A, B, C, …).
/// # **Arguments:**
/// - **`inputs`**: An iterator of items that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the logical OR of all input constraints.
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

/// The **`xor`** function takes two expressions and returns a new expression representing the logical XOR of the input expressions.
/// # **Arguments:**
/// - **`lhs`**: An expression or item that can be converted into **`Expr<F>`**.
/// - **`rhs`**: An expression or item that can be converted into **`Expr<F>`**.
/// # **Return:**
/// An **`Expr<F>`** representing the logical XOR of the input expressions.
pub fn xor<F: From<u64> + Clone, LHS: Into<Expr<F>>, RHS: Into<Expr<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Expr<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    lhs.clone() + rhs.clone() - 2u64.expr() * lhs * rhs
}

/// The **`eq`** function takes two constraints and returns a new constraint representing the equality of the input constraints.
/// # **Arguments:**
/// - **`lhs`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// - **`rhs`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the equality of the input constraints.
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

/// The **`select`** function takes a selector constraint and two other constraints, and returns a new constraint that represents the value of **`when_true`** if the selector is true, or **`when_false`** if the selector is false.
/// # **Arguments:**
/// - **`selector`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// - **`when_true`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// - **`when_false`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the conditional value based on the selector constraint.
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

/// The **`when`** function takes a selector constraint and a `when_true` constraint, and returns a new constraint that represents the value of **`when_true`** if the selector is true, or zero if the selector is false.
/// # **Arguments:**
/// - **`selector`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// - **`when_true`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the `when_true` value when the selector is true.
pub fn when<F: From<u64> + Clone, T1: Into<Constraint<F>>, T2: Into<Constraint<F>>>(
    selector: T1,
    when_true: T2,
) -> Constraint<F> {
    let selector = selector.into();
    let when_true = when_true.into();

    Constraint {
        annotation: format!("if({})then({})", selector.annotation, when_true.annotation),
        expr: selector.expr * when_true.expr,
    }
}

/// The **`unless`** function takes a selector constraint and a `when_false` constraint, and returns a new constraint that represents the value of **`when_false`** unless the selector is true, in which case it returns zero.
/// # **Arguments:**
/// - **`selector`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// - **`when_false`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the `when_false` value unless the selector is true.
pub fn unless<F: From<u64> + Clone, T1: Into<Constraint<F>>, T2: Into<Constraint<F>>>(
    selector: T1,
    when_false: T2,
) -> Constraint<F> {
    let selector = selector.into();
    let when_false = when_false.into();

    Constraint {
        annotation: format!(
            "unless({})then({})",
            selector.annotation, when_false.annotation
        ),
        expr: (1u64.expr() - selector.expr) * when_false.expr,
    }
}

/// The **`not`** function takes a constraint and returns a new constraint representing the logical NOT of the input constraint. The input constraint must have a value of either 0 or 1.
/// # **Arguments:**
/// - **`constraint`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the logical NOT of the input constraint.
pub fn not<F: From<u64>, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();
    let annotation = format!("NOT({})", constraint.annotation);
    let expr = 1u64.expr() - constraint.expr;

    Constraint { annotation, expr }
}

/// The **`isz`** function takes a constraint and returns a new constraint representing whether the input constraint is zero.
/// # **Arguments:**
/// - **`constraint`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing whether the input constraint is zero.
pub fn isz<F, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> {
    let constraint = constraint.into();

    Constraint {
        annotation: format!("0 == {}", constraint.annotation),
        expr: constraint.expr,
    }
}

/// The **`if_next_step`** function takes a **`StepTypeHandler`** and a constraint, and returns a new constraint that is only applied if the next step is of the given step type.
/// # **Arguments:**
/// - **`step_type`**: A **`StepTypeHandler`** object.
/// - **`constraint`**: A constraint or item that can be converted into **`Constraint<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** representing the conditional constraint based on the next step's type.
pub fn if_next_step<F: Clone, T: Into<Constraint<F>>>(
    step_type: StepTypeHandler,
    constraint: T,
) -> Constraint<F> {
    let constraint = constraint.into();

    let annotation = format!(
        "if(next step is {})then({})",
        step_type.annotation, constraint.annotation
    );

    Constraint {
        expr: step_type.next() * constraint.expr,
        annotation,
    }
}

/// The **`next_step_must_be`** function takes a **`StepTypeHandler`** and returns a new constraint that requires the next step to be of the given step type.
/// # **Arguments:**
/// - **`step_type`**: A **`StepTypeHandler`** object.
/// # **Return:**
/// A **`Constraint<F>`** representing the requirement that the next step must be of the given step type.
pub fn next_step_must_be<F: From<u64>>(step_type: StepTypeHandler) -> Constraint<F> {
    annotate(
        format!("next_step_must_be({})", step_type.annotation),
        not(step_type.next()),
    )
}

/// The **`next_step_must_not_be`** function takes a **`StepTypeHandler`** and returns a new constraint that requires the next step to not be of the given step type.
/// # **Arguments:**
/// - **`step_type`**: A **`StepTypeHandler`** object.
/// # **Return:**
/// A **`Constraint<F>`** representing the requirement that the next step must not be of the given step type.
pub fn next_step_must_not_be<F: From<u64>>(step_type: StepTypeHandler) -> Constraint<F> {
    annotate(
        format!("next_step_must_be({})", step_type.annotation),
        step_type.next(),
    )
}

/// The **`annotate`** function takes a string annotation and an expression, and returns a new constraint with the given annotation and expression.
/// # **Arguments:**
/// - **`annotation`**: A **`String`** containing the annotation for the constraint.
/// - **`expr`**: An expression or item that can be converted into **`Expr<F>`**.
/// # **Return:**
/// A **`Constraint<F>`** with the given annotation and expression.
pub fn annotate<F, E: Into<Expr<F>>>(annotation: String, expr: E) -> Constraint<F> {
    Constraint {
        annotation,
        expr: expr.into(),
    }
}

/// The **`rlc`** function computes the randomized linear combination of the given expressions and randomness.
/// # **Arguments:**
/// - **`exprs`**: A slice of expressions or items that can be converted into **`Expr<F>`**.
/// - **`randomness`**: A randomness value or item that can be converted into **`Expr<F>`**.
/// # **Return:**
/// An **`Expr<F>`** representing the randomized linear combination of the input expressions and randomness.
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

/// The **`LookupBuilder`** struct is a helper struct for building lookup tables.
pub struct LookupBuilder<F> {
    pub lookup: Lookup<F>,
}

impl<F> Default for LookupBuilder<F> {
    fn default() -> Self {
        LookupBuilder {
            lookup: Lookup::default(),
        }
    }
}

impl<F: Debug + Clone> LookupBuilder<F> {
    /// # **Description:**
    /// Adds a source column-lookup column pair to the lookup table. Can chain `**add**` and `**enable**` function calls to build the lookup table.
    /// # **Arguments:**
    /// - **`constraint`**: Source column that accepts any type that can be converted into a  **`Constraint<F>`**.
    /// - **`expression`**: Lookup column that accepts any type that can be converted into an **`Expr<F>`**.
    /// # **Return:**
    /// A mutable reference to the **`LookupBuilder<F>`**.
    pub fn add<C: Into<Constraint<F>>, E: Into<Expr<F>>>(
        &mut self,
        constraint: C,
        expression: E,
    ) -> &mut Self {
        let constraint = constraint.into();
        self.lookup
            .add(constraint.annotation, constraint.expr, expression.into());
        self
    }

    /// # **Description:**
    /// Adds a selector column specific to the lookup table. Can chain `**add**` and `**enable**` function calls to build the lookup table.
    /// # **Arguments:**
    /// - **`enable`**: Selector column that accepts any type that can be converted into **`Constraint<F>`**.
    /// # **Return:**
    /// A mutable reference to the **`LookupBuilder<F>`**.
    pub fn enable<C: Into<Constraint<F>>>(&mut self, enable: C) -> &mut Self {
        let enable = enable.into();
        self.lookup.enable(enable.annotation, enable.expr);
        self
    }
}

/// Creates a new empty **`LookupBuilder`** object and returns it. Can chain `**add**` and `**enable**` function calls to build the lookup table.
/// # **Return:**
/// A new empty **`LookupBuilder<F>`**. See more information about the **`LookupBuilder`** object and its functions for building the lookup table below.
pub fn lookup<F: Debug + Clone>() -> LookupBuilder<F> {
    LookupBuilder::default()
}
