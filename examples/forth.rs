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
    // | s1 | s2 | o | r |
    // |  1 |  1 | 1 | 2 |
    // |  3 |  2 | 3 | 6 |
    // |  4 |  2 | 4 | 2 |

    let forth = circuit::<(F, F), F>("FORTH", |ctx| {

        let s1 = ctx.forward("s1");
        let s2 = ctx.forward("s2");
        let o = ctx.forward("o");
        let r = ctx.forward("r");

        let operation_lookup: Queriable<(F, F)> = ctx.fixed("op lookup");

        // populate lookup column; this can be increased as more operations are added (e.g. 5 -> %, 6 -> ^, etc.)
        ctx.fixed_gen(move |ctx| {
            for i in 1..=4 {
                ctx.assign(i, operation_lookup, F::from(i as u64));
            }
        });

        // stack operation step
        let stack_step = ctx.step_type_def("stack step", |ctx| {
            ctx.setup(move |ctx| {
                // are matches allowed in circuit definitions?
                match o {
                    1 => {
                        ctx.constr(eq(s1 + s2, c));
                    }
                    2 => {
                        ctx.constr(eq(s1 - s2, c));
                    }
                    3 => {
                        ctx.constr(eq(s1 * s2, c));
                    }
                    4 => {
                        ctx.constr(eq(s1 / s2, c));
                    }
                    _ => {
                        panic!("invalid operation")
                    }
                }

                // initialize lookup
                ctx.add_lookup(lookup().add(o, operation_lookup));
            });
        });
    });
}