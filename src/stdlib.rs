use halo2_proofs::{arithmetic::Field, halo2curves::ff::PrimeField};

use crate::{
    ast::{query::Queriable, ToExpr, Expr},
    compiler::WitnessGenContext,
    dsl::{cb::{Constraint, lookup}, StepTypeContext},
};

use super::{
    util::{expr_from_bytes},
};

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
    diff: Vec<Queriable<F>>, // length is N_BYTES
    u8: Queriable<F>,
    range: u32,
}

impl<F: PrimeField, const N_BYTES: usize> Lt<F, N_BYTES> {
    pub fn setup<V: Into<Constraint<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        lhs: V,
        rhs: V,
        u8: Queriable<F>, // generated from import_halo2_fixed and assigned by fixed_gen at CircuitContext level
    ) -> Lt<F, N_BYTES> {
        let lhs: Constraint<F> = lhs.into();
        let rhs: Constraint<F> = rhs.into();
        let lt = ctx.internal("lt");
        let diff_bytes = (0..N_BYTES).map(|idx| ctx.internal(format!("diff{idx}").as_str())).collect(); // might need to differentiate the annotation of different columns later
        let range = 2u32.pow((N_BYTES * 8) as u32);
        
        // This gate enforces the constraint that the difference between lhs and rhs plus the result of the "less than" operation (lt) times the range equals the sum of the bytes represented by diff
        ctx.constr(lhs.expr - rhs.expr - expr_from_bytes(diff_bytes) + lt.clone() * range.expr()); // constr takes Queriable or Expr or Constraint
        // Additionally, it checks that lt is either 0 or 1, ensuring it's a boolean value.
        ctx.constr(lt * (1u64.expr() - lt));

        // lookup for each of the diff columns to constrain them to 0-255
        ctx.add_lookup(diff_bytes.iter().fold(&mut lookup::<F>(), |acc, x| acc.add(*x, u8)));

        Lt {
            lt, 
            diff: diff_bytes,
            u8,
            range,
        }
    }
    
    pub fn is_lt(&self) -> Constraint<F> {
        Constraint::from(self.lt.clone())
    }
}

impl<F: PrimeField<Repr = [u8; 32]>, const N_BYTES: usize> Lt<F, N_BYTES> {
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, lhs: F, rhs: F) {
        let lt = lhs < rhs;
        ctx.assign(self.lt, F::from(lt as u64));
        let diff: F = lhs - rhs + (if lt { F::from(self.range as u64) } else { F::ZERO });
        let diff_bytes: [u8; 32] = diff.to_repr(); // error should be fixed after we use eth_types::Field, which is a zkEVM package
        for (idx, diff) in self.diff.iter().enumerate() {
            ctx.assign(*diff, F::from(diff_bytes[idx] as u64));
        }
    }
}
