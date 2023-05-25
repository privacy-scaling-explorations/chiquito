use chiquito::{
    ast::{query::Queriable, Expr, ToExpr},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
        WitnessGenContext,
    },
    dsl::{circuit, StepTypeContext},
};
use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};

use std::fmt::Debug;

struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_expression: Expr<F>,
}

impl<F: Field + From<u64>> IsZero<F> {
    pub fn setup<V: Into<Expr<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Expr<F> = value.into();
        let is_zero_expression = (1.expr() - value.clone()) * value_inv;

        ctx.constr(value * is_zero_expression.clone());

        IsZero {
            value_inv,
            is_zero_expression,
        }
    }

    pub fn is_zero(&self) -> Expr<F> {
        self.is_zero_expression.clone()
    }
}

impl<F: Field> IsZero<F> {
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, value: F) {
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::ZERO));
    }
}

#[derive(Debug)]
struct BytecodeLine<F: Debug> {
    _hash: F,
    _index: F,
    _length: F,
    _is_code: F,
    _value: F,
    _push_data_left: F,
}

fn main() {
    let bytecode_circuit =
        circuit::<Fr, Vec<Vec<BytecodeLine<Fr>>>, BytecodeLine<Fr>, _>("bytecode circuit", |ctx| {
            use chiquito::dsl::cb::*;

            let length = ctx.forward("length");
            let index = ctx.forward("index");
            let is_code = ctx.forward("is_code");
            let value = ctx.forward("value");

            let s1 = ctx.step_type("header");
            ctx.step_type_def(s1, |ctx| {
                ctx.constr(isz(index));
                ctx.constr(eq(value, length));
            });
            let s2 = ctx.step_type("byte");
            ctx.step_type_def(s2, |ctx| {
                let push_data_left = ctx.internal("push_data_left");
                // let push_data_size = ctx.internal("push_data_size");
                let push_data_left_inv = ctx.internal("push_data_left_inv");

                let push_data_left_is_zero = IsZero::setup(ctx, push_data_left, push_data_left_inv);

                ctx.constr(eq(is_code, push_data_left_is_zero.is_zero()));

                // TODO
                // lookup(
                // (value, push_data_size_table.value)
                // (push_data_size, push_data_size_table.push_data_size)
                // )

                ctx.wg(move |ctx, _| {
                    push_data_left_is_zero.wg(ctx, Fr::zero());
                });
            });
        });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    println!("{:#?}", compiler.compile(&bytecode_circuit));
}
