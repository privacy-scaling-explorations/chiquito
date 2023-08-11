use halo2_proofs::dev::MockProver;
use halo2curves::bn256::Fr;

use chiquito::{
    ast::ToField,
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit},
    circuit,
    compiler::{cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder},
    ir::{assignments::AssignmentGenerator, Circuit},
};

fn fibo_circuit() -> (Circuit<Fr>, Option<AssignmentGenerator<Fr, ()>>) {
    let fibo = circuit!(fibonacci, {
        let a = forward!(a);
        let b = forward!("b");

        let fibo_step = step_type_def!(fibo_step {
            let c = internal!(c);

            setup!({
                require!(a + b => c);

                require!(transition b => a.next());

                require!(transition c => b.next());
            });

            wg!(a_value: u32, b_value: u32 {
                assign!(a => a_value.field());
                assign!(b => b_value.field());
                assign!(c => (a_value + b_value).field());
            })
        });

        pragma_num_steps!(11);

        trace!({
            add!(&fibo_step, (1, 1));
            let mut a = 1;
            let mut b = 2;

            for _i in 1..11 {
                add!(&fibo_step, (a, b));

                let prev_a = a;
                a = b;
                b += prev_a;
            }
        });
    });

    println!("=== AST ===\n{:#?}", fibo);

    chiquito::compiler::compile(
        chiquito::compiler::config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
        &fibo,
    )
}

fn main() {
    let (chiquito, wit_gen) = fibo_circuit();
    println!("=== IR ===\n{:#?}", chiquito);
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
}
