use std::hash::Hash;

use chiquito::{
    field::Field,
    frontend::dsl::{circuit, trace::DSLTraceGenerator}, /* main function for constructing an AST
                                                         * circuit */
    plonkish::{
        backend::halo2::{get_halo2_settings, halo2_prove, halo2_verify, OneNg},
        compiler::{
            cell_manager::SingleRowCellManager, // input for constructing the compiler
            compile,                            // input for constructing the compiler
            config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::{assignments::AssignmentGenerator, Circuit},
    }, /* compiles to
        * Chiquito Halo2
        * backend,
        * which can be
        * integrated into
        * Halo2
        * circuit */
    poly::ToField,
};
use halo2_proofs::halo2curves::bn256::Fr;
use rand_chacha::rand_core::block::BlockRng;

const MAX_FACTORIAL: usize = 10;

type AssignGen<F> = AssignmentGenerator<F, DSLTraceGenerator<F, u32>>;
fn generate<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssignGen<F>>) {
    // table for the circuit:
    // |    step_type      |  i  |  x   |
    // ----------------------------------
    // |  first_step       |  0  |  1   |
    // |  operation_step   |  1  |  1   |
    // |  operation_step   |  2  |  2   |
    // |  operation_step   |  3  |  6   |
    // |  result_step      |  4  |  24  |
    // |  result_step      |  4  |  24  |
    // |  result_step      |  4  |  24  |
    // ...

    use chiquito::frontend::dsl::cb::*; // functions for constraint building

    let factorial_circuit = circuit::<F, u32, _>("factorial", |ctx| {
        let i = ctx.shared("i");
        let x = ctx.forward("x");

        // first step will make sure the circuit is initialized correctly
        let first_step = ctx.step_type_def("first_step", |ctx| {
            // define the setup
            ctx.setup(move |ctx| {
                // constrain `i` to zero
                ctx.constr(eq(i, 0));
                // constrain `x` to one
                ctx.constr(eq(x, 1));
                // constrain the next `x` to be equal to the current `x`
                ctx.transition(eq(x, x.next()));
            });
            // witness assignment
            ctx.wg(move |ctx, ()| {
                ctx.assign(i, 0.into());
                ctx.assign(x, 1.into());
            })
        });

        // operation step will make sure every state transition is correct
        let operation_step = ctx.step_type_def("operation_step", |ctx| {
            // define the setup
            ctx.setup(move |ctx| {
                // constrain i.prev() + 1 == i
                ctx.transition(eq(i.rot(-1) + 1, i));
                // constrain i + 1 == i.next()
                ctx.transition(eq(i + 1, i.next()));
                // constrain the next `x` to be the product of the current `x` and the next `i`
                ctx.transition(eq(x * i.next(), x.next()));
            });
            // witness assignment
            ctx.wg(move |ctx, (i_value, x_value): (u32, u32)| {
                ctx.assign(i, i_value.field());
                ctx.assign(x, x_value.field());
            })
        });

        // result step will hold and propagate the value
        let result_step = ctx.step_type_def("result_step", |ctx| {
            // define the setup
            ctx.setup(move |ctx| {
                // constrain `i` to not change
                ctx.transition(eq(i, i.next()));
                // constrain `x` to not change
                ctx.transition(eq(x, x.next()));
            });
            // witness assignment
            ctx.wg(move |ctx, (i_value, x_value): (u32, u32)| {
                ctx.assign(i, i_value.field());
                ctx.assign(x, x_value.field());
            })
        });

        ctx.pragma_first_step(&first_step);
        ctx.pragma_last_step(&result_step);
        ctx.pragma_num_steps(MAX_FACTORIAL + 1);

        ctx.trace(move |ctx, n| {
            ctx.add(&first_step, ());

            let mut current_result = 1;

            for i in 1..n + 1 {
                current_result *= i;
                if i == n {
                    // we found the result
                    ctx.add(&result_step, (i, current_result));
                } else {
                    // more operations need to be done
                    ctx.add(&operation_step, (i, current_result));
                }
            }

            // if padding is needed, propagate final values
            ctx.padding(&result_step, || (n, current_result));
        })
    });

    compile(
        config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
        &factorial_circuit,
    )
}

// After compiling Chiquito AST to an IR, it is further parsed by a Chiquito Halo2 backend and
// integrated into a Halo2 circuit, which is done by the boilerplate code below.

// standard main function for a Halo2 circuit
fn main() {
    let plonkish = generate::<Fr>();
    let rng = BlockRng::new(OneNg {});

    let (cs, params, vk, pk, chiquito_halo2) = get_halo2_settings(10, plonkish.0, rng);

    let rng = BlockRng::new(OneNg {});
    let witness = plonkish.1.unwrap().generate(0);
    let instances = &chiquito_halo2.instance(&witness);
    let instance = if instances.is_empty() {
        vec![]
    } else {
        vec![instances.clone()]
    };
    let proof = halo2_prove(
        &params,
        pk,
        rng,
        cs,
        vec![&witness],
        vec![chiquito_halo2],
        instance.clone(),
    );

    let result = halo2_verify(proof, params, vk, instance);

    println!("result = {:#?}", result);

    if let Err(error) = &result {
        println!("{}", error);
    }

    let plonkish = generate::<Fr>();
    let rng = BlockRng::new(OneNg {});

    let (cs, params, vk, pk, chiquito_halo2) = get_halo2_settings(8, plonkish.0, rng);

    let rng = BlockRng::new(OneNg {});
    let witness = plonkish.1.unwrap().generate(7);
    let instances = &chiquito_halo2.instance(&witness);
    let instance = if instances.is_empty() {
        vec![]
    } else {
        vec![instances.clone()]
    };
    let proof = halo2_prove(
        &params,
        pk,
        rng,
        cs,
        vec![&witness],
        vec![chiquito_halo2],
        instance.clone(),
    );

    let result = halo2_verify(proof, params, vk, instance);

    println!("result = {:#?}", result);

    if let Err(error) = &result {
        println!("{}", error);
    }
}
