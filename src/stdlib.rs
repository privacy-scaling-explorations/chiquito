use std::hash::Hash;

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::{query::Queriable, ToExpr},
    frontend::dsl::{
        cb::{Constraint, Typing},
        StepTypeContext,
    },
    wit_gen::StepInstance,
};

pub struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_constraint: Constraint<F>,
}

impl<F: Field + From<u64>> IsZero<F> {
    pub fn setup<V: Into<Constraint<F>>>(
        ctx: &mut StepTypeContext<F>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Constraint<F> = value.into();
        let is_zero_expression = 1.expr() - (value.expr.clone() * value_inv);

        ctx.constr(value.expr.clone() * is_zero_expression.clone());

        let is_zero_constraint = Constraint {
            expr: is_zero_expression,
            annotation: format!("is_zero({:?})", value),
            typing: Typing::Boolean,
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

impl<F: Field + Eq + Hash> IsZero<F> {
    pub fn wg<WGC>(&self, ctx: &mut StepInstance<F>, value: F) {
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::ZERO));
    }
}
