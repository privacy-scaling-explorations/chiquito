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

// This example file extends the rust example file 'fibonacci.rs',
// describing usage of multiple steptypes, padding, and exposing signals.

// the main circuit function
fn fibo_circuit<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssignmentGenerator<F, u32>>)
// u32 is for external input that indicates the number of fibnoacci iterations
{
    use chiquito::{
        ast::ExposeOffset::*, // for exposing witnesses
        frontend::dsl::cb::*, // functions for constraint building
    };

    let fibo = circuit::<F, u32, _>("fibonacci", |ctx| {
        // Example table for 7 rounds:
        // |    step_type    |  a |  b |  c |  n |
        // ---------------------------------------
        // | fibo_first_step |  1 |  1 |  2 |  7 |
        // |    fibo_step    |  1 |  2 |  3 |  7 |
        // |    fibo_step    |  2 |  3 |  5 |  7 |
        //         ...
        // |    fibo_step    | 13 | 21 | 34 |  7 |
        // |     padding     | 21 | 34 |  . |  7 |
        // |     padding     | 21 | 34 |  . |  7 |
        //         ...

        // define forward signals
        let a = ctx.forward("a");
        let b = ctx.forward("b");
        let n = ctx.forward("n");

        // define step types

        // For soundness, set "a" and "b" both 1 in the first step instance
        let fibo_first_step = ctx.step_type_def("fibo first step", |ctx| {
            // define internal signals
            let c = ctx.internal("c");

            // set constraints of the step
            ctx.setup(move |ctx| {
                // constr: constrains internal signals only
                // a == 1
                ctx.constr(eq(a, 1));
                // b == 1
                ctx.constr(eq(b, 1));
                // a + b == c
                ctx.constr(eq(a + b, c));

                // transition: can constrain forward signals
                // b == a.next
                ctx.transition(eq(b, a.next()));
                // c == b.next
                ctx.transition(eq(c, b.next()));
                // n == n.next
                ctx.transition(eq(n, n.next()));
            });

            // define wg function to set how to assign witness values
            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!(
                    "first fibo line wg: a: {}, b: {}, c: {}, n: {}",
                    a_value,
                    b_value,
                    a_value + b_value,
                    n_value
                );
                // a <- a_value
                ctx.assign(a, a_value.field());
                // b <- b_value
                ctx.assign(b, b_value.field());
                // c <- a_value + b_value
                ctx.assign(c, (a_value + b_value).field());
                // n <- n_value
                ctx.assign(n, n_value.field());
            })
        });

        // Regular Fibonacci step
        let fibo_step = ctx.step_type_def("fibo step", |ctx| {
            let c = ctx.internal("c");

            ctx.setup(move |ctx| {
                // a + b == c
                ctx.constr(eq(a + b, c));

                // b == a.next
                ctx.transition(eq(b, a.next()));
                // c == b.next
                ctx.transition(eq(c, b.next()));
                // n == n.next
                ctx.transition(eq(n, n.next()));
            });

            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!(
                    "fib line wg: a: {}, b: {}, c: {}, n: {}",
                    a_value,
                    b_value,
                    a_value + b_value,
                    n_value
                );
                // a <- a_value
                ctx.assign(a, a_value.field());
                // b <- b_value
                ctx.assign(b, b_value.field());
                // c <- a_value + b_value
                ctx.assign(c, (a_value + b_value).field());
                // n <- n_value
                ctx.assign(n, n_value.field());
            })
        });

        // For flexibility of number of steps, add paddings to maximum number of steps
        let padding = ctx.step_type_def("padding", |ctx| {
            ctx.setup(move |ctx| {
                // b == b.next
                ctx.transition(eq(b, b.next()));
                // n == n.next
                ctx.transition(eq(n, n.next()));
            });

            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!("padding: a: {}, b: {}, n: {}", a_value, b_value, n_value);

                // Note that although "a" is not needed for padding,
                // we have to assign "a" because fibo_step constrains 'b == a.next'
                // a <- a_value
                ctx.assign(a, a_value.field());
                // b <- b_value
                ctx.assign(b, b_value.field());
                // n <- n_value
                ctx.assign(n, n_value.field());
            })
        });

        // set total number of steps
        ctx.pragma_num_steps(11);
        // constrain steptype of first step
        ctx.pragma_first_step(&fibo_first_step);
        // constrain steptype of last step
        ctx.pragma_last_step(&padding);
        // Note that because we constrain last step to be padding, the maximum number of
        // Fibonacci sequence is 10. (one less than num_steps above)

        // Expose the result of calculation and round number
        ctx.expose(b, Last);
        ctx.expose(n, Last);

        // define how to use step instantiations from external input
        ctx.trace(move |ctx, n| {
            // add a step instantiation, which calls wg function with given args
            ctx.add(&fibo_first_step, (1, 1, n));
            let mut a = 1;
            let mut b = 2;

            for _i in 1..n {
                ctx.add(&fibo_step, (a, b, n));

                let prev_a = a;
                a = b;
                b += prev_a;
            }

            // use padding function for padding step, which automatically
            // fills empty steps to fit num_steps
            ctx.padding(&padding, || (a, b, n));
        })
    });

    compile(
        config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
        &fibo,
    )
}

// After compiling Chiquito AST to an IR, it is further parsed by a Chiquito Halo2 backend and
// integrated into a Halo2 circuit, which is done by the boilerplate code below.

// standard main function for a Halo2 circuit
fn main() {
    let (chiquito, wit_gen) = fibo_circuit::<Fr>();
    let compiled = chiquito2Halo2(chiquito);
    let circuit = ChiquitoHalo2Circuit::new(compiled, wit_gen.map(|g| g.generate(7)));

    let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

    let result = prover.verify_par();

    println!("{:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }

    // plaf boilerplate
    use chiquito::plonkish::backend::plaf::chiquito2Plaf;
    use polyexen::plaf::{backends::halo2::PlafH2Circuit, WitnessDisplayCSV};

    // get Chiquito ir
    let (circuit, wit_gen) = fibo_circuit::<Fr>();
    // get Plaf
    let (plaf, plaf_wit_gen) = chiquito2Plaf(circuit, 8, false);
    let wit = plaf_wit_gen.generate(wit_gen.map(|v| v.generate(7)));

    // debug only: print witness
    println!("{}", WitnessDisplayCSV(&wit));

    // get Plaf halo2 circuit from Plaf's halo2 backend
    // this is just a proof of concept, because Plaf only has backend for halo2
    // this is unnecessary because Chiquito has a halo2 backend already
    let plaf_circuit = PlafH2Circuit { plaf, wit };

    let plaf_instance = vec![vec![34.field(), 7.field()]];
    // same as halo2 boilerplate above
    let prover_plaf = MockProver::<Fr>::run(8, &plaf_circuit, plaf_instance).unwrap();

    let result_plaf = prover_plaf.verify_par();

    println!("result = {:#?}", result_plaf);

    if let Err(failures) = &result_plaf {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}
