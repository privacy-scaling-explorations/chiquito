use chiquito::{
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit}, 
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
use halo2_proofs::dev::MockProver;
use halo2curves::{bn256::Fr, ff::Field};
use std::{cell::RefCell, hash::Hash, rc::Rc};

// Generic types:
// (F, F, F) are the elements that are in the stack along with the result of the operation
fn forth_circuit<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssigmentGenerator<F, ()>>) {
    // PLONKish table for the FORTH stack:
    // | s1 | s2  | r |
    // |  1 |  1  | 2 | <- where step type is add
    // |  3 |  2  | 6 | <- where step type is mul
    // |  4 |  2  | 2 | <- where step type is sub

    let forth = circuit::<F, (), (F, F, F), _>("FORTH", |ctx| {
        // declare signals
        let s1 = Rc::new(RefCell::new(ctx.forward("s1")));
        let s2 = Rc::new(RefCell::new(ctx.forward("s2")));
        let r = Rc::new(RefCell::new(ctx.forward("r")));

        ctx.pragma_num_steps(3);

        let add_step = ctx.step_type_def("add", |ctx| {
            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.setup(move |ctx| {
                ctx.constr(eq(
                    *s1_cloned.borrow() + *s2_cloned.borrow(),
                    *r_cloned.borrow(),
                ));
            });

            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.wg(move |ctx, (s1_value, s2_value, r_value): (F, F, F)| {
                ctx.assign(*s1_cloned.borrow(), s1_value);
                ctx.assign(*s2_cloned.borrow(), s2_value);
                ctx.assign(*r_cloned.borrow(), r_value);
            })
        });

        let sub_step = ctx.step_type_def("sub", |ctx| {
            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.setup(move |ctx| {
                ctx.constr(eq(
                    *s1_cloned.borrow() - *s2_cloned.borrow(),
                    *r_cloned.borrow(),
                ));
            });

            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.wg(move |ctx, (s1_value, s2_value, r_value): (F, F, F)| {
                ctx.assign(*s1_cloned.borrow(), s1_value);
                ctx.assign(*s2_cloned.borrow(), s2_value);
                ctx.assign(*r_cloned.borrow(), r_value);
            })
        });

        let mul_step = ctx.step_type_def("mul", |ctx| {
            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.setup(move |ctx| {
                ctx.constr(eq(
                    *s1_cloned.borrow() * *s2_cloned.borrow(),
                    *r_cloned.borrow(),
                ));
            });

            let s1_cloned = s1.clone();
            let s2_cloned = s2.clone();
            let r_cloned = r.clone();

            ctx.wg(move |ctx, (s1_value, s2_value, r_value): (F, F, F)| {
                ctx.assign(*s1_cloned.borrow(), s1_value);
                ctx.assign(*s2_cloned.borrow(), s2_value);
                ctx.assign(*r_cloned.borrow(), r_value);
            })
        });

        ctx.trace(move |ctx: _, _| {
            // 1 + 1 = 2
            ctx.add(&add_step, (F::from(1u64), F::from(1u64), F::from(2u64)));
            // 5 - 4 = 1
            ctx.add(&sub_step, (F::from(5u64), F::from(4u64), F::from(1u64)));
            // 2 * 3 = 6
            ctx.add(&mul_step, (F::from(2u64), F::from(3u64), F::from(6u64)));
        });
    });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    compiler.compile(&forth)
}

fn main() {
    let (chiquito, wit_gen) = forth_circuit::<Fr>();
    let compiled = chiquito2Halo2(chiquito);
    let circuit = ChiquitoHalo2Circuit::new(compiled, wit_gen.map(|g| g.generate(())));

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
