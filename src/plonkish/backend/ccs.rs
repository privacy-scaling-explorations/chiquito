

use std::hash::Hash;

use halo2_proofs::{arithmetic::Field, plonk::Assignment};

use crate::{
    plonkish::ir::{Circuit, assignments::Assignments},
    util::UUID,
    ccs::circuit::CCSCircuit,
};


pub struct ChiquitoCCS<F: Field + From<u64>> {
    pub debug: bool,
    circuit: Circuit<F>,
    ir_id: UUID,
    // ccs: 
}

impl<F: Field + From<u64> + Hash> ChiquitoCCS<F> {
    pub fn new(circuit: Circuit<F>) -> ChiquitoCCS<F> {
        let ir_id = circuit.ast_id;
        Self {
            debug: true,
            circuit,
            ir_id,
        }
    }

    pub fn configure(&mut self) {

    }
}


pub struct ChiquitoCCSCircuit<F: Field + From<u64>> {
    compiled: ChiquitoCCS<F>,
    witness: Option<Assignments<F>>,
}

impl <F: Field + From<u64> + Hash> ChiquitoCCSCircuit<F> {
    pub fn new(compiled: ChiquitoCCS<F>, witness: Option<Assignments<F>>) -> Self {
        Self { compiled, witness }
    }

    pub fn instance(&self) {
        
    }
}


#[allow(non_snake_case)]
pub fn chiquito2CCS<F: Field + From<u64> + Hash>(circuit: Circuit<F>) -> ChiquitoCCS<F> {
    ChiquitoCCS::new(circuit)
}