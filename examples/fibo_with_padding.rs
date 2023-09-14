use std::hash::Hash;

use chiquito::{
    ast::expr::*,
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
};
use halo2_proofs::{arithmetic::Field, dev::MockProver, halo2curves::bn256::Fr};

// the main circuit function: returns the compiled IR of a Chiquito circuit
// Generic types F, (), (u64, 64) stand for:
// 1. type that implements a field trait
// 2. empty trace arguments, i.e. (), because there are no external inputs to the Chiquito circuit
// 3. two witness generation arguments both of u64 type, i.e. (u64, u64)
fn fibo_circuit<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssignmentGenerator<F, u32>>)
{
    // PLONKish table for the Fibonacci circuit:
    // | a | b | c |
    // | 1 | 1 | 2 |
    // | 1 | 2 | 3 |
    // | 2 | 3 | 5 |
    // | 3 | 5 | 8 |
    // ...

    use chiquito::frontend::dsl::cb::*; // functions for constraint building

    let fibo = circuit::<F, u32, _>("fibonacci", |ctx| {
        // the following objects (forward signals, steptypes) are defined on the circuit-level

        // forward signals can have constraints across different steps
        let a = ctx.forward("a");
        let b = ctx.forward("b");
        let n = ctx.forward("n");

        let fibo_first_step = ctx.step_type_def("fibo first step", |ctx| {
            let c = ctx.internal("c");

            ctx.setup(move |ctx| {
                ctx.constr(eq(a, 1));
                ctx.constr(eq(b, 1));
                ctx.constr(eq(a + b, c));
                ctx.transition(eq(b, a.next()));
                ctx.transition(eq(c, b.next()));
                ctx.transition(eq(n, n.next()));
            });

            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!(
                    "first fibo line wg: a: {}, b: {}, c: {}, n: {}",
                    a_value,
                    b_value,
                    a_value + b_value,
                    n_value
                );
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(c, (a_value + b_value).field());
                ctx.assign(n, n_value.field());
            })
        });

        // define step type
        let fibo_step = ctx.step_type_def("fibo step", |ctx| {
            // the following objects (constraints, transition constraints, witness generation
            // function) are defined on the step type-level

            // internal signals can only have constraints within the same step
            let c = ctx.internal("c");

            // in setup we define the constraints of the step
            ctx.setup(move |ctx| {
                // regular constraints are for internal signals only
                // constrain that a + b == c by calling `eq` function from constraint builder
                ctx.constr(eq(a + b, c));

                // transition constraints accepts forward signals as well
                // constrain that b is equal to the next instance of a, by calling `next` on forward
                // signal
                ctx.transition(eq(b, a.next()));
                // constrain that c is equal to the next instance of c, by calling `next` on forward
                // signal
                ctx.transition(eq(c, b.next()));

                ctx.transition(eq(n, n.next()));
            });

            // witness generation (wg) function is Turing complete and allows arbitrary user defined
            // logics for assigning witness values wg function is defined here but no
            // witness value is assigned yet
            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!(
                    "fib line wg: a: {}, b: {}, c: {}, n: {}",
                    a_value,
                    b_value,
                    a_value + b_value,
                    n_value
                );
                // assign arbitrary input values from witness generation function to witnesses
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(c, (a_value + b_value).field());

                ctx.assign(n, n_value.field());
            })
        });

        let padding = ctx.step_type_def("padding", |ctx| {
            ctx.setup(move |ctx| {
                ctx.transition(eq(b, b.next()));
                ctx.transition(eq(n, n.next()));
            });

            ctx.wg(move |ctx, (a_value, b_value, n_value): (u32, u32, u32)| {
                println!("padding: a: {}, b: {}, n: {}", a_value, b_value, n_value);

                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(n, n_value.field());
            })
        });

        ctx.pragma_num_steps(11);
        ctx.pragma_first_step(&fibo_first_step);
        ctx.pragma_last_step(&padding);

        ctx.expose(b, chiquito::ast::ExposeOffset::Last);
        ctx.expose(n, chiquito::ast::ExposeOffset::Last);

        // trace function is responsible for adding step instantiations defined in step_type_def
        // function above trace function is Turing complete and allows arbitrary user
        // defined logics for assigning witness values
        ctx.trace(move |ctx, n| {
            // add function adds a step instantiation to the main circuit and calls witness
            // generation function defined in step_type_def input values for witness
            // generation function are (1, 1) in this step instance
            ctx.add(&fibo_first_step, (1, 1, n));
            let mut a = 1;
            let mut b = 2;

            for _i in 1..n {
                ctx.add(&fibo_step, (a, b, n));

                let prev_a = a;
                a = b;
                b += prev_a;
            }

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