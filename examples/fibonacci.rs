use chiquito::{
    ast::expr::*,
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2}, /* compiles to Chiquito Halo2 backend,
                                                      * which can be integrated into Halo2
                                                      * circuit */
    compiler::{
        cell_manager::{MaxWidthCellManager, SingleRowCellManager}, /* input for constructing the compiler */
        step_selector::SimpleStepSelectorBuilder, // input for constructing the compiler
        Compiler,                                 // compiles AST to IR
    },
    dsl::{
        cb::*,   // functions for constraint building
        circuit, // main function for constructing an AST circuit
    },
    ir::Circuit, // IR object that the compiler compiles to
};
use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    halo2curves::{bn256::Fr, FieldExt},
    plonk::ConstraintSystem,
};

// the main circuit function: returns the compiled IR of a Chiquito circuit
// Generic types F, (), (u64, 64) stand for:
// 1. type that implements a field trait
// 2. empty trace arguments, i.e. (), because there are no external inputs to the Chiquito circuit
// 3. two witness generation arguments both of u64 type, i.e. (u64, u64)
fn fibo_circuit<F: FieldExt>() -> (Circuit<F, (), (u64, u64)>, Circuit<F, (), (u64, u64)>) {
    // PLONKish table for the Fibonacci circuit:
    // | a | b | c |
    // | 1 | 1 | 2 |
    // | 1 | 2 | 3 |
    // | 2 | 3 | 5 |
    // | 3 | 5 | 8 |
    // ...
    let fibo = circuit::<F, (), (u64, u64), _>("fibonacci", |ctx| {
        // the following objects (forward signals, steptypes) are defined on the circuit-level

        // forward signals can have constraints across different steps
        let a = ctx.forward("a");
        let b = ctx.forward("b");

        // initiate step type for future definition
        let fibo_step = ctx.step_type("fibo step");
        let fibo_last_step = ctx.step_type("last step");

        // enforce step type of the first step
        ctx.pragma_first_step(fibo_step);
        // enforce step type of the last step
        ctx.pragma_last_step(fibo_last_step);

        // define step type
        ctx.step_type_def(fibo_step, |ctx| {
            // the following objects (constraints, transition constraints, witness generation
            // function) are defined on the step type-level

            // internal signals can only have constraints within the same step
            let c = ctx.internal("c");

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

            // witness generation (wg) function is Turing complete and allows arbitrary user defined
            // logics for assigning witness values wg function is defined here but no
            // witness value is assigned yet
            ctx.wg(move |ctx, (a_value, b_value)| {
                println!("fib line wg: {} {} {}", a_value, b_value, a_value + b_value);
                // assign arbitrary input values from witness generation function to witnesses
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());
                ctx.assign(c, (a_value + b_value).field());
            });
        });

        ctx.step_type_def(fibo_last_step, |ctx| {
            let c = ctx.internal("c");

            // constrain that a + b == c by calling `eq` function from constraint builder
            // no transition constraint needed for the next instances of a and b, because it's the
            // last step
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

        // trace function is responsible for adding step instantiations defined in step_type_def
        // function above trace function is Turing complete and allows arbitrary user
        // defined logics for assigning witness values
        ctx.trace(move |ctx, _| {
            // add function adds a step instantiation to the main circuit and calls witness
            // generation function defined in step_type_def input values for witness
            // generation function are (1, 1) in this step instance
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

    // single row cell manager places all signals of a step instance in one PLONKish table row, i.e.
    // all super rows are height 1
    let compiler_single_row = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
    // max width cell manager customizes the maximum column width of step instances and adjust the
    // number of PLONKish table rows accordingly
    let compiler_max_width = Compiler::new(
        MaxWidthCellManager { max_width: 1 },
        SimpleStepSelectorBuilder {},
    );

    (
        compiler_single_row.compile(&fibo),
        compiler_max_width.compile(&fibo),
    )
}

// After compiling Chiquito AST to an IR, it is further parsed by a Chiquito Halo2 backend and
// integrated into a Halo2 circuit, which is done by the boilerplate code below.

// *** Halo2 boilerplate ***
#[derive(Clone)]
struct FiboConfig<F: FieldExt> {
    // ChiquitoHalo2 object in the bytecode circuit config struct
    compiled: ChiquitoHalo2<F, (), (u64, u64)>,
}

impl<F: FieldExt> FiboConfig<F> {
    fn new(meta: &mut ConstraintSystem<F>, cell_manager: String) -> FiboConfig<F> {
        // chiquito2Halo2 function in Halo2 backend can convert ir::Circuit object to a
        // ChiquitoHalo2 object, which can be further integrated into a Halo2 circuit in the
        // example below
        let mut compiled = if cell_manager == "single_row" {
            chiquito2Halo2(fibo_circuit::<F>().0)
        } else {
            // MaxWidthCellManager with max_width = 1
            chiquito2Halo2(fibo_circuit::<F>().1)
        };

        // ChiquitoHalo2 objects have their own configure and synthesize functions defined in the
        // Chiquito Halo2 backend
        compiled.configure(meta);

        FiboConfig { compiled }
    }
}

macro_rules! impl_fibo_circuit {
    ($circuit_struct:ident, $cell_manager:expr) => {
        #[derive(Default)]
        struct $circuit_struct {}

        impl<F: FieldExt> halo2_proofs::plonk::Circuit<F> for $circuit_struct {
            type Config = FiboConfig<F>;

            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
                FiboConfig::<F>::new(meta, $cell_manager.to_string())
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
    };
}

impl_fibo_circuit!(FiboCircuitSingleRowCellManager, "single_row");
impl_fibo_circuit!(FiboCircuitMaxWidthCellManager, "max_width");

macro_rules! run_circuit {
    ($circuit_type:ty) => {{
        let circuit = <$circuit_type>::default();

        let prover = MockProver::<Fr>::run(7, &circuit, Vec::new()).unwrap();

        let result = prover.verify_par();

        println!("{:#?}", result);

        if let Err(failures) = &result {
            for failure in failures.iter() {
                println!("{}", failure);
            }
        }
    }};
}

// standard main function for a Halo2 circuit
fn main() {
    run_circuit!(FiboCircuitSingleRowCellManager);
    run_circuit!(FiboCircuitMaxWidthCellManager);
}
