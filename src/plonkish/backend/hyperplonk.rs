use plonkish_backend::backend::{
    hyperplonk::{HyperPlonk},
    PlonkishCircuit,
};
use plonkish_backend::{
    frontend::halo2::{CircuitExt, Halo2Circuit},
    pcs::multilinear::MultilinearKzg,
    util::transcript::Keccak256Transcript,
};
use halo2_proofs::halo2curves::bn256::Fr;


// pub fn 

// #[test]
// fn vanilla_plonk_circuit_info() {
//     let circuit = Halo2Circuit::new::<HyperPlonk<()>>(3, ());
//     let circuit_info = circuit.circuit_info().unwrap();
// }