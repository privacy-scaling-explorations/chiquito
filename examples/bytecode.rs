use chiquito::{
    ast::{query::Queriable, Expr, ToExpr},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
        WitnessGenContext,
    },
    dsl::{circuit, StepTypeContext},
};
use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{bn256::Fr, FieldExt},
};

use std::fmt::Debug;

struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_expression: Expr<F>,
}

impl<F: FieldExt> IsZero<F> {
    pub fn setup<V: Into<Expr<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Expr<F> = value.into();
        let is_zero_expression = (1.expr() - value.clone()) * value_inv;

        ctx.constr("isZero", value.clone() * is_zero_expression.clone());

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
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::zero()));
    }
}

#[derive(Debug)]
struct BytecodeLine<F: Debug> {
    hash: F,
    index: F,
    length: F,
    is_code: F,
    value: F,
    push_data_left: F,
}

fn main() {
    let mut bytecode_circuit =
        circuit::<Fr, Vec<Vec<BytecodeLine<Fr>>>, BytecodeLine<Fr>, _>("bytecode circuit", |ctx| {
            let length = ctx.forward("length");
            let index = ctx.forward("index");
            let hash = ctx.forward("hash");
            let is_code = ctx.forward("is_code");
            let value = ctx.forward("value");
            let value_rlc = ctx.forward("value_rlc");

            let s1 = ctx.step_type("header");
            ctx.step_type_def(s1, |ctx| {
                ctx.constr("index == 0", index.expr());
                ctx.constr("value == length", value.expr());

                ctx.wg(|ctx, v| {})
            });
            let s2 = ctx.step_type("byte");
            ctx.step_type_def(s2, |ctx| {
                let push_data_left = ctx.signal("push_data_left");
                let push_data_size = ctx.signal("push_data_size");
                let push_data_left_inv = ctx.signal("push_data_left_inv");

                let push_data_left_is_zero = IsZero::setup(ctx, push_data_left, push_data_left_inv);

                ctx.constr(
                    "is_code == push_data_left_is_zero.is_zero",
                    is_code - push_data_left_is_zero.is_zero(),
                );

                // TODO
                // lookup(
                // (value, push_data_size_table.value)
                // (push_data_size, push_data_size_table.push_data_size)
                // )

                ctx.wg(move |ctx, _| {
                    push_data_left_is_zero.wg(ctx, Fr::zero());
                });
            });

            ctx.trace(|ctx, bytecodes| {
                for bytecode in bytecodes {
                    println!("todo");
                }
            })
        });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    println!("{:#?}", compiler.compile(&mut bytecode_circuit));
}
