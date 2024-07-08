use ark_bn254::{Fr as FFr, G1Projective as Projective};
use ark_ff::BigInt;
use halo2_proofs::halo2curves::{bn256::Fr, ff::PrimeField};
use std::hash::Hash;

use chiquito::{
    ccs::{
        backend::ccs::{chiquito2CCS, ChiquitoCCSCircuit},
        compiler::{
            cell_manager::SingleRowCellManager,
            compile, // input for constructing the compiler
            config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::{assignments::AssignmentGenerator, circuit::Circuit},
    },
    field::Field,
    frontend::dsl::circuit,
    poly::ToField,
    sbpir::SBPIR,
};

use folding_schemes::{
    ccs::CCS,
    commitment::{pedersen::Pedersen, CommitmentScheme},
    folding::hypernova::nimfs::NIMFS,
    transcript::{
        poseidon::{poseidon_canonical_config, PoseidonTranscript},
        Transcript,
    },
};

// the main circuit function: returns the compiled IR of a Chiquito circuit
// Generic types F, (), (u64, 64) stand for:
// 1. type that implements a field trait
// 2. empty trace arguments, i.e. (), because there are no external inputs to the Chiquito circuit
// 3. two witness generation arguments both of u64 type, i.e. (u64, u64)

type FiboReturn<F> = (Circuit<F>, Option<AssignmentGenerator<F, ()>>, SBPIR<F, ()>);

fn fibo_circuit_ccs<F: Field + From<u64> + Hash>() -> FiboReturn<F> {
    // PLONKish table for the Fibonacci circuit:
    // | a | b | c |
    // | 1 | 1 | 2 |
    // | 1 | 2 | 3 |
    // | 2 | 3 | 5 |
    // | 3 | 5 | 8 |
    // ...

    use chiquito::frontend::dsl::cb::*; // functions for constraint building

    let fibo = circuit::<F, (), _>("fibonacci", |ctx| {
        // the following objects (forward signals, steptypes) are defined on the circuit-level

        // forward signals can have constraints across different steps
        let a = ctx.forward("a");
        let b = ctx.forward("b");

        // define step type
        let fibo_step = ctx.step_type_def("fibo step", |ctx| {
            // the following objects (constraints, transition constraints, witness generation
            // function) are defined on the step type-level

            // internal signals can only have constraints within the same step
            let c = ctx.internal("c");

            // in setup we define the constraints of the step
            ctx.setup(move |ctx| {
                // regular constraints are for signals without rotation only

                // `auto_eq` creates a constraint and also auto generates the witness of the left
                // side.
                ctx.auto_eq(c, a + b);

                // transition constraints accepts forward signals as well
                // constrain that b is equal to the next instance of a by calling `eq` function from
                // constraint builder and `next` on forward signal
                ctx.transition(eq(b, a.next()));
                // constrain that c is equal to the next instance of c, by calling `next` on forward
                // signal
                ctx.transition(eq(c, b.next()));
            });

            // witness generation (wg) function is Turing complete and allows arbitrary user defined
            // logics for assigning witness values wg function is defined here but no
            // witness value is assigned yet
            ctx.wg(move |ctx, (a_value, b_value): (u32, u32)| {
                // println!("fib line wg: {} {} {}", a_value, b_value, a_value + b_value);
                // assign arbitrary input values from witness generation function to witnesses
                ctx.assign(a, a_value.field());
                ctx.assign(b, b_value.field());

                // c is auto generated by `auto_eq`
            })
        });

        ctx.pragma_num_steps(16);

        // trace function is responsible for adding step instantiations defined in step_type_def
        // function above trace function is Turing complete and allows arbitrary user
        // defined logics for assigning witness values
        ctx.trace(move |ctx: _, _| {
            // add function adds a step instantiation to the main circuit and calls witness
            // generation function defined in step_type_def input values for witness
            // generation function are (1, 1) in this step instance
            ctx.add(&fibo_step, (1, 1));
            let mut a = 1;
            let mut b = 2;

            for _i in 1..16 {
                ctx.add(&fibo_step, (a, b));

                let prev_a = a;
                a = b;
                b += prev_a;
            }
        })
    });

    let compiled = compile(
        config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
        &fibo,
    );

    (compiled.0, compiled.1, fibo)
}

fn main() {
    let (chiquito, wit_gen, _) = fibo_circuit_ccs::<Fr>();
    let compiled = chiquito2CCS(chiquito);

    let circuit = ChiquitoCCSCircuit::new(compiled, wit_gen.map(|g| g.generate(())));

    let (ccs, z) = circuit.configure();
    let result = ccs.is_satisfied(&z);
    println!("fibonacci {:#?}", result);

    let (chiquito, wit_gen, _) = fibo_circuit_ccs::<Fr>();
    let compiled = chiquito2CCS(chiquito);
    let circuit = ChiquitoCCSCircuit::new(compiled, wit_gen.map(|g| g.generate(())));
    let (circuit, z) = circuit.configure();

    let ccs = circuit.convert_to_sonobe_circuit(fr_convert);
    let inputs = z.convert_to_sonobe_inputs(fr_convert);

    let result = ccs.check_relation(&inputs);
    println!("sonobe fibonacci = {:?}", result);

    run_hypernova(ccs, inputs);
}

fn run_hypernova(ccs: CCS<FFr>, z: Vec<FFr>) {
    use ark_ff::PrimeField;

    let mut rng = ark_std::test_rng();
    let n: usize = 64;
    // setup params
    let (params, _) = Pedersen::<Projective>::setup(&mut rng, n).unwrap();

    let (running_instance, running_wit) = ccs.to_lcccs(&mut rng, &params, &z).unwrap();
    let res = running_instance.check_relation(&params, &ccs, &running_wit);
    println!("sonobe fibonacci lcccs check_relation = {:?}", res);

    let (new_instance, new_wit) = ccs.to_cccs(&mut rng, &params, &z).unwrap();
    let res = new_instance.check_relation(&params, &ccs, &new_wit);
    println!("sonobe fibonacci cccs check_relation = {:?}", res);

    // Prover's transcript
    let poseidon_config = poseidon_canonical_config::<FFr>();
    let mut transcript_p: PoseidonTranscript<Projective> =
        PoseidonTranscript::<Projective>::new(&poseidon_config);
    transcript_p.absorb(&FFr::from_le_bytes_mod_order(b"init init"));

    let (proof, folded_lcccs, folded_witness) =
        NIMFS::<Projective, PoseidonTranscript<Projective>>::prove(
            &mut transcript_p,
            &ccs,
            &[running_instance.clone()],
            &[new_instance.clone()],
            &[running_wit],
            &[new_wit],
        )
        .unwrap();

    // Verifier's transcript
    let mut transcript_v: PoseidonTranscript<Projective> =
        PoseidonTranscript::<Projective>::new(&poseidon_config);
    transcript_v.absorb(&FFr::from_le_bytes_mod_order(b"init init"));

    let folded_lcccs_v = NIMFS::<Projective, PoseidonTranscript<Projective>>::verify(
        &mut transcript_v,
        &ccs,
        &[running_instance.clone()],
        &[new_instance.clone()],
        proof,
    )
    .unwrap();
    println!("sonobe hypernova verify...ok");

    assert_eq!(folded_lcccs, folded_lcccs_v);
    let res = folded_lcccs.check_relation(&params, &ccs, &folded_witness);
    println!("sonobe fibonacci folded lcccs check_relation = {:?}", res);
}

fn fr_convert(r: &Fr) -> FFr {
    let converted = (0..4)
        .map(|i| {
            let mut values = [0u8; 8];
            values.copy_from_slice(&r.to_repr().as_ref()[i * 8..i * 8 + 8]);
            u64::from_le_bytes(values)
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    FFr::from(BigInt::new(converted))
}
