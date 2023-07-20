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
// 1) F for a type that implements the field element trait
// 2) (u64, u64) are the elements that are in the stack; the stack is made up of two signals with many steps so each basic operation consumes 1 step
// 3) u8 for the operation; we will map 1 -> +, 2 -> -, 3 -> *, 4 -> /
// 4) u64 for the result of the operation
fn forth_circuit<F: Field + From<u64>>() -> (Circuit<F>, Option<AssigmentGenerator<F, ()>>) {
    // PLONKish table for the FORTH stack:
    // | s1 | s2 | o | r |
    // |  1 |  1 | 1 | 2 |
    // |  3 |  2 | 3 | 6 |
    // |  4 |  2 | 4 | 2 |

    
}