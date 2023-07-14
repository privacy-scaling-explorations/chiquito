use crate::ir::{sc::SuperCircuit, Circuit};

pub struct Linker {}

impl Linker {
    pub fn link<F>(units: Vec<Circuit<F>>) -> SuperCircuit<F> {
        let sc = SuperCircuit::default();
    }
}
