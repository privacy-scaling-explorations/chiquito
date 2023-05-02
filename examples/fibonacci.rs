use chiquito::{
    ast::ToField,
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::circuit,
};
use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    halo2curves::{bn256::Fr, FieldExt},
    plonk::ConstraintSystem,
};

fn fibo_circuit<F: FieldExt>() -> chiquito::ir::Circuit<F, (), (u64, u64)> {
    let fibo = circuit::<F, (), (u64, u64), _>("fibonacci", |ctx| {
        use chiquito::dsl::cb::*;

        let a = ctx.forward("a");
        let b = ctx.forward("b");

        let fibo_step = ctx.step_type("fibo step");
        let fibo_last_step = ctx.step_type("last step");

        ctx.pragma_first_step(fibo_step);
        ctx.pragma_last_step(fibo_last_step);

        ctx.step_type_def(fibo_step, |ctx| {
            let c = ctx.internal("c");

            ctx.constr(eq(a + b, c));
            ctx.transition(eq(b, a.next()));
            ctx.transition(eq(c, b.next()));

            ctx.wg(move |ctx, (a_value, b_value)| {
                println!("fib line wg: {} {} {}", a_value, b_value, a_value + b_value);
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(c, (a_value + b_value).field());
            });
        });

        ctx.step_type_def(fibo_last_step, |ctx| {
            let c = ctx.internal("c");

            ctx.constr(eq(a + b, c));

            ctx.wg(move |ctx, (a_value, b_value)| {
                println!(
                    "fib last line wg: {} {} {}",
                    a_value,
                    b_value,
                    a_value + b_value
                );
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(c, (a_value + b_value).field());
            });
        });

        ctx.trace(move |ctx, _| {
            ctx.add(&fibo_step, (1, 1));
            let mut a = 1;
            let mut b = 2;

            for _i in 1..10 {
                ctx.add(&fibo_step, (a, b));

                let prev_a = a;
                a = b;
                b += prev_a;
            }

            ctx.add(&fibo_last_step, (a, b));
        })
    });


    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    compiler.compile(&fibo)

}

fn main() {
    let circuit = FiboCircuit {};

    let prover = MockProver::<Fr>::run(7, &circuit, Vec::new()).unwrap();

    let result = prover.verify_par();

    println!("{:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

// *** Halo2 boilerplate ***

#[derive(Clone)]
struct FiboConfig<F: FieldExt> {
    compiled: ChiquitoHalo2<F, (), (u64, u64)>,
}

impl<F: FieldExt> FiboConfig<F> {
    fn new(meta: &mut ConstraintSystem<F>) -> FiboConfig<F> {
        let mut compiled = chiquito2Halo2(fibo_circuit::<F>());

        compiled.configure(meta);

        FiboConfig { compiled }
    }
}

#[derive(Default)]
struct FiboCircuit {}

impl<F: FieldExt> halo2_proofs::plonk::Circuit<F> for FiboCircuit {
    type Config = FiboConfig<F>;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
        FiboConfig::<F>::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        config.compiled.synthesize(&mut layouter, ());

        Ok(())
    }
}
