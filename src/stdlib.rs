use halo2_proofs::{arithmetic::Field, halo2curves::ff::PrimeField};

use crate::{
    ast::{query::Queriable, ToExpr},
    compiler::WitnessGenContext,
    dsl::{
        cb::{lookup, Constraint},
        StepTypeContext,
    },
};

use super::util::expr_from_bytes;

pub struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_constraint: Constraint<F>,
}

impl<F: Field + From<u64>> IsZero<F> {
    pub fn setup<V: Into<Constraint<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Constraint<F> = value.into();
        let is_zero_expression = 1.expr() - (value.expr.clone() * value_inv);

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

pub struct Lt<F, const N_BYTES: usize> {
    lt: Queriable<F>,
    diff: Vec<Queriable<F>>, // Byte representation of diff. Length is N_BYTES.
    range: u32,
}

impl<F: PrimeField, const N_BYTES: usize> Lt<F, N_BYTES> {
    pub fn setup<V: Into<Constraint<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        lhs: V,
        rhs: V,
        u8: Queriable<F>, // Fix column imported from Halo2 and assigned by fixed_gen lambda.
    ) -> Lt<F, N_BYTES> {
        let lhs: Constraint<F> = lhs.into();
        let rhs: Constraint<F> = rhs.into();
        let lt = ctx.internal("lt");
        let diff_bytes: Vec<Queriable<F>> = (0..N_BYTES)
            .map(|idx| ctx.internal(format!("diff {idx}").as_str()))
            .collect();
        let range = 2u32.pow((N_BYTES * 8) as u32);

        // Enforce that the difference between lhs and rhs plus the result of the "less than"
        // operation (`lt`) times the range equals the sum of diff's byte representation.
        ctx.constr(lhs.expr - rhs.expr - expr_from_bytes(diff_bytes.clone()) + lt * range.expr());
        // Enforce that lt is a Boolean value.
        ctx.constr(lt * (1u64.expr() - lt));

        // Enforce that diff's byte representation all fall within 0-255.
        ctx.add_lookup(
            diff_bytes
                .iter()
                .fold(&mut lookup::<F>(), |acc, x| acc.add(*x, u8)),
        );

        Lt {
            lt,
            diff: diff_bytes,
            range,
        }
    }

    pub fn is_lt(&self) -> Constraint<F> {
        Constraint::from(self.lt)
    }
}

impl<F: PrimeField<Repr = [u8; 32]> + Ord, const N_BYTES: usize> Lt<F, N_BYTES> {
    // Ord trait is required to compare F values and generate `lt`.
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, lhs: F, rhs: F) {
        let lt = lhs < rhs;
        ctx.assign(self.lt, F::from(lt as u64));
        let diff: F = lhs - rhs
            + (if lt {
                F::from(self.range as u64)
            } else {
                F::ZERO
            });
        let diff_bytes: [u8; 32] = diff.to_repr();
        for (idx, diff) in self.diff.iter().enumerate() {
            ctx.assign(*diff, F::from(diff_bytes[idx] as u64));
        }
    }
}
