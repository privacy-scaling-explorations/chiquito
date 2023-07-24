use chiquito::{
    ast::expr::*,
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit}, /* compiles to
                                                             * Chiquito Halo2
                                                             * backend,
                                                             * which can be
                                                             * integrated into
                                                             * Halo2
                                                             * circuit */
    compiler::{
        cell_manager::SingleRowCellManager, // input for constructing the compiler
        step_selector::SimpleStepSelectorBuilder, // input for constructing the compiler
        Compiler,
    },
    dsl::{
        cb::*,   // functions for constraint building
        circuit, // main function for constructing an AST circuit
    },
    ir::{assigments::AssigmentGenerator, Circuit}, // compiled circuit type
};
use halo2curves::{ff::Field, bn256::Fr};

// Generic types:
// 1) (F, F) are the elements that are in the stack; the stack is made up of two signals with many steps so each basic operation consumes 1 step
// 3) F for the result of the operation
fn forth_circuit<F: Field + From<u64>>() -> (Circuit<F>, Option<AssigmentGenerator<F, ()>>) {
    // PLONKish table for the FORTH stack:
    // | s1 | s2  | r |
    // |  1 |  1  | 2 |
    // |  3 |  2  | 6 |
    // |  4 |  2  | 2 |

    let forth = circuit::<(F, F), F>("FORTH", |ctx| {

        // declare signals
        let s1 = ctx.forward("s1");
        let s2 = ctx.forward("s2");
        let r = ctx.forward("r");

        // initialize steps
        let add_step = ctx.step_type("add");
        let sub_step = ctx.step_type("sub");
        let mul_step = ctx.step_type("mul");
        let div_step = ctx.step_type("div");

        // first step type: Since it's a general VM, do we need an ordering to the steps?
        ctx.pragma_first_step(add_step);
        // last step type
        ctx.pragma_last_step(div_step);
        // total number of steps: Should this be arbitrary?
        ctx.pragma_num_steps(4);

        // addition operation step
        let add_step = ctx.step_type_def("add", |ctx| {
            ctx.setup(move |ctx| {
                ctx.constr(eq(s1 + s2, r));
            });

            ctx.wg(move |ctx, (s1_value, s2_value, r_value): (F, F, F)| {
                println!("add step: s1: {}, s2: {}, r: {}", s1_value, s2_value, r_value);
                ctx.assign(s1, s1_value);
                ctx.assign(s2, s2_value);
                ctx.assign(r, r_value);
            })
        });

        // subtraction operation step
        let sub_step = ctx.step_type_def("sub", |ctx| {
            ctx.setup(move |ctx| {
                ctx.constr(eq(s1 - s2, r));
            });

            ctx.wg(move |ctx, (s1_value, s2_value, r_value): (F, F, F)| {
                println!("sub step: s1: {}, s2: {}, r: {}", s1_value, s2_value, r_value);
                ctx.assign(s1, s1_value);
                ctx.assign(s2, s2_value);
                ctx.assign(r, r_value);
            })
        });

        // multiplication operation step
        let mul_step = ctx.step_type_def("mul", |ctx| {
            ctx.setup(move |ctx| {
                ctx.constr(eq(s1 * s2, r));
            });

            ctx.wg(|ctx, (s1_result, s2_result, r_result): (F, F, F)| {
                println!("mul step: s1: {}, s2: {}, r: {}", s1_result, s2_result, r_result);
                ctx.assign(s1, s1_result);
                ctx.assign(s2, s2_result);
                ctx.assign(r, r_result);
            })
        });

        // division operation step
        let div_step = ctx.step_type_def("div", |ctx| {
            ctx.setup(move |ctx| {
                ctx.constr(eq(s1 / s2, r));
            });

            ctx.wg(|ctx, (s1_result, s2_result, r_result): (F, F, F)| {
                println!("div step: s1: {}, s2: {}, r: {}", s1_result, s2_result, r_result);
                ctx.assign(s1, s1_result);
                ctx.assign(s2, s2_result);
                ctx.assign(r, r_result);
            })
        });

        ctx.trace(move |ctx: _, _| {
            // Here we fill the circuit with the constraint 1 + 1 = 2
            ctx.add(&add_step, (1, 1, 2));
            // 5 - 4 = 1
            ctx.add(&sub_step, (5, 4, 1));
            // 2 * 3 = 6
            ctx.add(&mul_step, (2, 3, 6));
            // 4 / 2 = 2
            ctx.add(&div_step, (4, 2, 2));
        });
    });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    compiler.compile(&forth)

}

fn main() {
    let (chiquito, wit_gen) = forth_circuit::<Fr>();
    let compiled = chiquito2Halo2(chiquito);
    // passing 0 as the TraceArgs argument for g.generate as somewhat of a placeholder since TraceArgs aren't used in this example
    let circuit = ChiquitoHalo2Circuit::new(compiled, wit_gen.map(|g| g.generate(0)));
    println!("Compiled circuit: {:?}", circuit);

    let prover = MockProver::<Fr>::run(7, &circuit, Vec::new()).unwrap();

    let result = prover.verify_par();

    println!("{:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }

    // Is the plaf boilerplate required?
}