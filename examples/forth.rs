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
use halo2curves::ff::Field;

// Generic types:
// 1) (F, F) are the elements that are in the stack; the stack is made up of two signals with many steps so each basic operation consumes 1 step
// 2) F for the operation; we will map 1 -> +, 2 -> -, 3 -> *, 4 -> / ; these will be constrained with a lookup table
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

        // stack operation step
        let stack_step = ctx.step_type_def("stack step", |ctx| {
            ctx.setup(move |ctx| {
            });
        });

        // addition operation step type
        let add_step = ctx.step_type_def("add", |ctx| {
            ctx.setup(move |ctx| {
                let s1 = ctx.query(s1);
                let s2 = ctx.query(s2);
                let r = ctx.query(r);
                let add = ctx.query("add");
                let add = ctx.lookup(add, vec![s1, s2], r);
                ctx.assign(add, r);
            });
        });
    });
}