// use halo2_proofs::{arithmetic::Field, halo2curves::FieldExt};
use halo2_proofs::halo2curves::group::ff::Field;

use crate::{
    ast::{query::Queriable, ToExpr, Expr},
    compiler::WitnessGenContext,
    dsl::{cb::Constraint, StepTypeContext},
};

pub struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_constraint: Constraint<F>,
}

impl<F: Field> IsZero<F> {
    pub fn setup<V: Into<Constraint<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Constraint<F> = value.into();
        let is_zero_expression = Expr::Const(F::ONE) - (value.expr.clone() * value_inv);

        ctx.constr(value.expr.clone() * is_zero_expression.clone());

        let is_zero_constraint = Constraint {
            expr: is_zero_expression,
            annotation: format!("is_zero({:?})", value),
        };

        IsZero {
            value_inv,
            is_zero_constraint,
        }
    }

    pub fn is_zero(&self) -> Constraint<F> {
        self.is_zero_constraint.clone()
    }
}

impl<F: Field> IsZero<F> {
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, value: F) {
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::ZERO));
    }
}
