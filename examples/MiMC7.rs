use chiquito::{
    ast::query::Queriable,
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::circuit,
};
use halo2_proofs::{
    // arithmetic::Field,
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    halo2curves::{bn256::Fr, FieldExt, group::ff::PrimeField},
    plonk::{ConstraintSystem, Fixed, Column},
};
use chiquito::dsl::cb::*;
use MiMC7_constants::ROUND_KEYS;

// MiMC7 always has 91 rounds
pub const ROUNDS: usize = 91;

fn mimc7_circuit<F: FieldExt>(
    row_value: Column<Fixed>, // row index i, a fixed column allocated in circuit config, used as the first column of lookup table
    c_value: Column<Fixed>,  // round constant C_i, fixed column allocated in circuit config, used as the second column of lookup table
) -> chiquito::ir::Circuit<F, (F, F), (F, F, F, F)> {
    // circuit takes two trace arguments (x_in: F, k: F), i.e. message x_in and secret key k, as inputs
    // circuit also takes four step arguments (x: F, k: F, c: F, row: F), i.e. iterator x_{i+1} = (x_i+k_i+c_i)^7, secret key k, round constant c_i, and row index, as inputs
    let mimc7 = circuit::<F, (F, F), (F, F, F, F), _>("mimc7", |ctx| {
        // forward signals are referenced across different steps, e.g. between the current step and the next step
        let x = ctx.forward("x");
        let k = ctx.forward("k");
        let c = ctx.forward("c");
        let row = ctx.forward("row");
        
        let mimc7_first_step = ctx.step_type("mimc7 first step");
        let mimc7_step = ctx.step_type("mimc7 step");
        let mimc7_last_step = ctx.step_type("mimc7 last step");

        // convert halo2 columns to queriable columns defined in Chiquito
        let lookup_row: Queriable<F> = ctx.import_halo2_fixed("lookup row", row_value);
        let lookup_c: Queriable<F> = ctx.import_halo2_fixed("lookup row", c_value);
        
        // populate the lookup columns
        ctx.fixed_gen(move |ctx| {
            for i in 0..ROUNDS {
                ctx.assign(i, lookup_row, F::from(i as u64));
                ctx.assign(i, lookup_c, F::from_str_vartime(ROUND_KEYS[i]).unwrap());
            }
        });

        // step 0: 
        // input message x_in and secret key k
        // calculate the current iteration x_{i+1} = y_i = (x_i+k_i+c_i)^7
        // constrain that the secret key k doesn't change between steps
        // constrain the current row number to zero and the next row number to increment by one
        // constrain row number and round constant to match the lookup table
        ctx.step_type_def(mimc7_first_step, |ctx| {
            
            let xkc =  ctx.internal("xkc");
            let y =  ctx.internal("y");

            ctx.constr(eq(x + k + c, xkc));
            ctx.constr(eq(xkc * xkc * xkc * xkc * xkc * xkc * xkc, y));

            ctx.transition(eq(y, x.next()));
            ctx.transition(eq(k, k.next()));
            ctx.transition(eq(row, 0));
            ctx.transition(eq(row + 1, row.next()));

            ctx.add_lookup(lookup().add(row, lookup_row).add(c, lookup_c));

            ctx.wg(move |ctx, (x_value, k_value, c_value, row_value)| {
                ctx.assign(x, x_value);
                ctx.assign(k, k_value);
                ctx.assign(c, c_value);
                ctx.assign(row, row_value);

                let xkc_value = x_value + k_value + c_value;
                ctx.assign(xkc, xkc_value);
                ctx.assign(y, xkc_value.pow_vartime(&[7 as u64]));
            });
        });

        // step 1 through 90:
        // the same as step 0, except that row number isn't constrained to 0
        ctx.step_type_def(mimc7_step, |ctx| {
            
            let xkc =  ctx.internal("xkc");
            let y =  ctx.internal("y");

            ctx.constr(eq(x + k + c, xkc));
            ctx.constr(eq(xkc * xkc * xkc * xkc * xkc * xkc * xkc, y));

            ctx.transition(eq(y, x.next()));
            ctx.transition(eq(k, k.next()));
            ctx.transition(eq(row + 1, row.next()));

            ctx.add_lookup(lookup().add(row, lookup_row).add(c, lookup_c));

            ctx.wg(move |ctx, (x_value, k_value, c_value, row_value)| {
                ctx.assign(x, x_value);
                ctx.assign(k, k_value);
                ctx.assign(c, c_value);
                ctx.assign(row, row_value);

                let xkc_value = x_value + k_value + c_value;
                ctx.assign(xkc, xkc_value);
                ctx.assign(y, xkc_value.pow_vartime(&[7 as u64]));
            });
        });

        // step 90
        // not really a step, but only outputs the final result as x+k
        ctx.step_type_def(mimc7_last_step, |ctx| {
           
            let out = ctx.internal("out");

            ctx.constr(eq(x + k, out));

            ctx.wg(move |ctx, (x_value, k_value, _, row_value)| {
                ctx.assign(x, x_value);
                ctx.assign(k, k_value);
                // row value is overflowed to 91 here (should cap at 90), and is only generated to satisfy constraint from the previous step
                ctx.assign(row, row_value); 
                ctx.assign(out, x_value + k_value);
            });
        });

        // ensure types of the first and last steps
        ctx.pragma_first_step(mimc7_first_step);
        ctx.pragma_last_step(mimc7_last_step);

        ctx.trace(move |ctx, (x_in_value, k_value)| {
            // step 0: calculate witness values from trace inputs, i.e. message x_in and secret key k
            // note that c_0 == 0
            let mut c_value: F = F::from_str_vartime(ROUND_KEYS[0]).unwrap();
            let mut x_value = x_in_value;
            let mut row_value = F::from(0);
            // step 0: assign witness values
            ctx.add(&mimc7_first_step, (x_in_value, k_value, c_value, row_value));

            for i in 1..ROUNDS {
                // step 1 through 90: calculate witness values from iteration results
                row_value += F::from(1);
                x_value += k_value + c_value;
                x_value = x_value.pow_vartime(&[7 as u64]);
                c_value = F::from_str_vartime(ROUND_KEYS[i]).unwrap(); 
                // Step 1 through 90: assign witness values
                ctx.add(&mimc7_step, (x_value, k_value, c_value, row_value));
            }

            // step 90: calculate final output
            row_value += F::from(1);
            x_value += k_value + c_value;
            x_value = x_value.pow_vartime(&[7 as u64]);
            // Step 90: output the hash result as x + k in witness generation
            // output is not displayed as a public column, which will be implemented in the future
            ctx.add(&mimc7_last_step, (x_value, k_value, c_value, row_value)); // c_value is not used here but filled for consistency
        })
    });

    // println!("{:#?}", mimc7);
    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
    let compiled = compiler.compile(&mimc7);
    // println!("compiled = {:#?}", compiled);

    compiled
}


// * Halo2 boilerplate *
#[derive(Clone)]
struct Mimc7Config<F: FieldExt> {
    compiled: ChiquitoHalo2<F, (F, F), (F, F, F, F)>, // halo2 backend object
}

impl<F: FieldExt> Mimc7Config<F> {
    fn new(meta: &mut ConstraintSystem<F>) -> Mimc7Config<F> {
        let row_value = meta.fixed_column();
        let c_value = meta.fixed_column();

        let mut compiled = chiquito2Halo2(mimc7_circuit::<F>(row_value, c_value));
        compiled.configure(meta); // allocate columns to halo2 backend object

        Mimc7Config { compiled }
    }
}

#[derive(Default)]
struct Mimc7Circuit<F: FieldExt> { // define trace inputs
    x_in_value: F,
    k_value: F,
}

impl<F: FieldExt> halo2_proofs::plonk::Circuit<F> for Mimc7Circuit<F> {
    type Config = Mimc7Config<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
        Mimc7Config::<F>::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        config.compiled.synthesize(&mut layouter, (self.x_in_value, self.k_value));
        Ok(())
    }
}

fn main() {
    let circuit = Mimc7Circuit { // fill in trace inputs
        x_in_value: Fr::from_str_vartime("1").expect("expected a number"),
        k_value: Fr::from_str_vartime("2").expect("expected a number"),
    };

    let prover = MockProver::<Fr>::run(10, &circuit, Vec::new()).unwrap();

    let result = prover.verify_par();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

mod MiMC7_constants;