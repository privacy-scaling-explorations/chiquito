// use ark_bn254::Fr as FFr;
use ark_ff::PrimeField;
use ark_std::log2;
use folding_schemes::{ccs::CCS, utils::vec::dense_matrix_to_sparse};

use super::ccs::{CCSCircuit, Z};
use crate::field::Field;

impl<F: Field> CCSCircuit<F> {
    pub fn convert_to_sonobe_circuit<Fr: PrimeField>(&self, f: fn(&F) -> Fr) -> CCS<Fr> {
        let matrics = self
            .matrics
            .iter()
            .map(|matrix| {
                let values = matrix
                    .values()
                    .iter()
                    .map(|values| values.iter().map(f).collect())
                    .collect();
                dense_matrix_to_sparse(values)
            })
            .collect();
        let selectors = self
            .selectors
            .iter()
            .map(|selectors| selectors.iter().map(|(idx, _)| *idx).collect())
            .collect();
        CCS {
            m: self.m,
            n: self.n,
            l: self.l,
            t: self.t,
            q: self.q,
            d: self.d,
            s: log2(self.m) as usize,
            s_prime: log2(self.n) as usize,
            M: matrics,
            S: selectors,
            c: (0..self.q).map(|_| Fr::from(1u64)).collect(),
        }
    }
}

impl<F: Field> Z<F> {
    pub fn convert_to_sonobe_inputs<Fr: PrimeField>(&self, f: fn(&F) -> Fr) -> Vec<Fr> {
        let values = [
            vec![F::from(1u64)],
            self.assignments.clone(),
            self.public_inputs.clone(),
        ]
        .concat();
        values.iter().map(f).collect()
    }
}
