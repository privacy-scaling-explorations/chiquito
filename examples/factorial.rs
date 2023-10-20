use std::hash::Hash;

use chiquito::{
    field::Field,
    frontend::dsl::circuit, // main function for constructing an AST circuit
    plonkish::backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit}, /* compiles to
                             * Chiquito Halo2
                             * backend,
                             * which can be
                             * integrated into
                             * Halo2
                             * circuit */
    plonkish::compiler::{
        cell_manager::SingleRowCellManager, // input for constructing the compiler
        compile,                            // input for constructing the compiler
        config,
        step_selector::SimpleStepSelectorBuilder,
    },
    plonkish::ir::{assignments::AssignmentGenerator, Circuit}, // compiled circuit type
    poly::ToField,
};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

const MAX_FACTORIAL: usize = 10;

fn generate<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssignmentGenerator<F, u32>>) {
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
    let (chiquito, wit_gen) = generate::<Fr>();
    let compiled = chiquito2Halo2(chiquito);
    let circuit = ChiquitoHalo2Circuit::new(compiled, wit_gen.map(|g| g.generate(0)));

    let prover = MockProver::<Fr>::run(10, &circuit, circuit.instance()).unwrap();

    let result = prover.verify_par();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }

    // plaf boilerplate
    use chiquito::plonkish::backend::plaf::chiquito2Plaf;
    use polyexen::plaf::backends::halo2::PlafH2Circuit;

    // get Chiquito ir
    let (circuit, wit_gen) = generate::<Fr>();
    // get Plaf
    let (plaf, plaf_wit_gen) = chiquito2Plaf(circuit, 8, false);
    let wit = plaf_wit_gen.generate(wit_gen.map(|v| v.generate(7)));

    // debug only: print witness
    // println!("{}", polyexen::plaf::WitnessDisplayCSV(&wit));

    // get Plaf halo2 circuit from Plaf's halo2 backend
    // this is just a proof of concept, because Plaf only has backend for halo2
    // this is unnecessary because Chiquito has a halo2 backend already
    let plaf_circuit = PlafH2Circuit { plaf, wit };

    // same as halo2 boilerplate above
    let prover_plaf = MockProver::<Fr>::run(8, &plaf_circuit, Vec::new()).unwrap();

    let result_plaf = prover_plaf.verify_par();

    println!("result = {:#?}", result_plaf);

    if let Err(failures) = &result_plaf {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}
