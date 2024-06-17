use std::{collections::HashMap, hash::Hash};

use crate::{
    ccs::ir::{
        assignments::{Assignments, StepsID},
        circuit::Circuit,
    },
    field::Field,
    util::UUID,
};

pub type PositionMap = HashMap<(usize, u128), usize>;

#[allow(non_snake_case)]
pub fn chiquito2CCS<F: Field + From<u64> + Hash>(circuit: Circuit<F>) -> ChiquitoCCS<F> {
    ChiquitoCCS::new(circuit)
}

pub struct ChiquitoCCS<F: Field + From<u64>> {
    pub debug: bool,
    pub circuit: Circuit<F>,
    pub ir_id: UUID,
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
}

pub struct ChiquitoCCSCircuit<F: Field + From<u64>> {
    pub compiled: ChiquitoCCS<F>,
    pub steps_id: Option<StepsID>,
    pub witness: Option<Assignments<F>>,
}

impl<F: Field + From<u64> + Hash> ChiquitoCCSCircuit<F> {
    pub fn new(
        compiled: ChiquitoCCS<F>,
        witness: Option<Assignments<F>>,
        steps_id: Option<StepsID>,
    ) -> Self {
        Self {
            compiled,
            witness,
            steps_id,
        }
    }

    pub fn instance(&self) -> HashMap<(usize, UUID), F> {
        if !self.compiled.circuit.exposed.is_empty() {
            if let Some(witness) = &self.witness {
                return self.compiled.circuit.instance(witness);
            }
        }
        HashMap::new()
    }

    fn export_matrix_vec(
        &self,
        n: usize,
        num: usize,
        witness_pos: &PositionMap,
    ) -> (Vec<Matrix<F>>, usize) {
        let mut m = self.num_poly();
        let mut matrix_vec = vec![Matrix::new(n, m); num];
        let mut row = 0;
        if let Some(steps_id) = self.steps_id.as_ref() {
            for (idx, step_id) in steps_id.0.iter().enumerate() {
                // step
                let matrics = self.compiled.circuit.matrics.get(step_id).unwrap();

                for matrics in matrics.iter() {
                    // poly
                    if idx == steps_id.0.len() - 1 {
                        let mut skip = false;
                        for (matrics, _) in matrics.iter() {
                            if skip {
                                break;
                            }
                            for (_, _, next) in matrics.concat().iter() {
                                if *next {
                                    skip = true;
                                    break;
                                }
                            }
                        }
                        if skip {
                            m -= 1;
                            continue;
                        }
                    }

                    for (matrix_chunks, index) in matrics.iter() {
                        // chunk
                        assert!(*index <= self.compiled.circuit.selectors.len());
                        let selectors = self.compiled.circuit.selectors[*index].clone();
                        assert_eq!(matrix_chunks.len(), selectors.len());

                        for (items, (selector, _)) in matrix_chunks.iter().zip(selectors.iter()) {
                            // one row in on matrix
                            let mut values: Vec<(usize, usize, F)> = Vec::new();
                            for (v, id, next) in items.iter() {
                                let idx = if *next { idx + 1 } else { idx };
                                let col = if *id == 0 {
                                    witness_pos.get(&(0, 0))
                                } else {
                                    witness_pos.get(&(idx, *id))
                                };
                                match col {
                                    None => continue,
                                    Some(col) => values.push((row, *col, *v)),
                                }
                            }
                            matrix_vec[*selector].write(&values);
                        }
                    }
                    row += 1;
                }
            }
        };

        for matrix in matrix_vec.iter_mut() {
            if row < matrix.m {
                matrix.remove_rows(row);
            }
        }
        (matrix_vec, m)
    }

    fn num_poly(&self) -> usize {
        self.steps_id
            .as_ref()
            .map(|steps_idx| {
                steps_idx
                    .0
                    .iter()
                    .map(|idx| self.compiled.circuit.matrics.get(idx).unwrap().len())
                    .sum()
            })
            .unwrap()
    }

    fn coeffs_offsets(&self) -> (PositionMap, PositionMap) {
        let mut witness_pos = HashMap::new();
        let mut offset = 0;
        witness_pos.insert((0, 0), offset);
        offset += 1;
        if let Some(steps_id) = self.steps_id.as_ref() {
            for (idx, step_idx) in steps_id.0.iter().enumerate() {
                let witnesses = self.compiled.circuit.witness.get(step_idx).unwrap();
                for id in witnesses.iter() {
                    witness_pos.insert((idx, *id), offset);
                    offset += 1;
                }
            }
        }
        let mut public_pos = HashMap::new();
        for (idx, id) in self.compiled.circuit.exposed.iter() {
            public_pos.insert((*idx, *id), offset);
            offset += 1;
        }
        // todo: remove public values
        (witness_pos, public_pos)
    }
}

impl<F: Field + From<u64> + Hash> ChiquitoCCSCircuit<F> {
    pub fn configure(&self) -> (CCSCircuit<F>, Z<F>) {
        let (ccs, witness_pos, public_pos) = CCSCircuit::from_circuit(self);
        let mut z: Z<F> = Z::new(ccs.n, ccs.l);

        z.write(
            &self.instance(),
            self.witness.as_deref().unwrap(),
            &witness_pos,
            &public_pos,
        );
        (ccs, z)
    }
}

#[derive(Default)]
pub struct CCSCircuit<F> {
    pub n: usize,
    pub m: usize,
    pub l: usize,
    pub t: usize,
    pub q: usize,
    pub d: usize,
    pub matrics: Vec<Matrix<F>>,
    pub selectors: Vec<Vec<(usize, F)>>,
    pub constants: Vec<F>,
}

impl<F: Field + From<u64> + Hash> CCSCircuit<F> {
    pub fn new(n: usize, m: usize, t: usize, q: usize, l: usize, d: usize) -> Self {
        assert!(n > l);

        let matrics = Vec::new();
        let selectors = (0..q).map(|_| Vec::new()).collect();
        let constants = (0..q).map(|_| F::ZERO).collect();

        Self {
            n,
            m,
            l,
            t,
            q,
            d,
            matrics,
            selectors,
            constants,
        }
    }

    pub fn from_circuit(circuit: &ChiquitoCCSCircuit<F>) -> (Self, PositionMap, PositionMap) {
        let selectors = circuit.compiled.circuit.selectors.clone();
        let constants = (0..circuit.compiled.circuit.q).map(|_| F::ONE).collect();

        let mut matrix_num = 0;
        for selector in selectors.iter() {
            for (idx, _) in selector.iter() {
                matrix_num = matrix_num.max(*idx + 1);
            }
        }

        let (witness_pos, public_pos) = circuit.coeffs_offsets();
        let n = witness_pos.len() + public_pos.len();

        let (matrix_vec, m) = circuit.export_matrix_vec(n, matrix_num, &witness_pos);

        (
            Self {
                n,
                m,
                l: public_pos.len(),
                t: circuit.compiled.circuit.t,
                q: circuit.compiled.circuit.q,
                d: circuit.compiled.circuit.d,
                matrics: matrix_vec,
                selectors,
                constants,
            },
            witness_pos,
            public_pos,
        )
    }

    pub fn public_num(&self) -> usize {
        self.l
    }

    pub fn witness_num(&self) -> usize {
        self.n - self.l - 1
    }

    pub fn write(
        &mut self,
        matrics: &[Vec<(usize, usize, F)>],
        selectors: &[Vec<(usize, F)>],
        constants: &[F],
    ) {
        self.write_constants(constants);
        self.write_selectors_and_degree(selectors);
        self.write_matrics(matrics);
    }

    pub fn write_constants(&mut self, constants: &[F]) {
        assert_eq!(constants.len(), self.q);
        self.constants = constants.to_owned().clone();
    }

    pub fn write_selectors_and_degree(&mut self, selectors: &[Vec<(usize, F)>]) {
        let mut degree = 0;
        assert_eq!(selectors.len(), self.q);
        for selector in selectors.iter() {
            for &(s, _) in selector {
                assert!(s < self.t)
            }
            degree = degree.max(selector.len())
        }
        self.selectors = selectors.to_owned().clone();
        self.d = degree;
    }

    fn write_matrics(&mut self, matrics: &[Vec<(usize, usize, F)>]) {
        assert_eq!(matrics.len(), self.t);

        self.matrics = matrics
            .iter()
            .map(|cells| {
                for &cell in cells.iter() {
                    assert!(cell.0 < self.m);
                    assert!(cell.1 < self.n);
                }

                let mut matrix = Matrix::new(self.n, self.m);
                matrix.write(cells);
                matrix
            })
            .collect();
    }

    pub fn is_satisfied(&self, z: &Z<F>) -> bool {
        assert_eq!(self.selectors.len(), self.q);
        assert_eq!(self.constants.len(), self.q);

        let mut witnesses = z.assignments.clone();
        let mut inputs = z.public_inputs.clone();

        let mut values = vec![F::ONE];
        values.append(&mut inputs);
        values.append(&mut witnesses);

        let prod_vec: Vec<Vec<F>> = self
            .constants
            .iter()
            .zip(self.selectors.iter())
            .map(|(&c, selector)| {
                let hadamard_prod_vec: Vec<Vec<F>> = selector
                    .iter()
                    .map(|&(s, _)| {
                        assert!(s < self.matrics.len());
                        self.matrics[s].matrix_vector_product(&values)
                    })
                    .collect();
                hadamard_prod_vec
                    .iter()
                    .fold(vec![c; self.m], |acc, vec| hadamard_product(&acc, vec))
            })
            .collect();
        let sum_vec = vec_add(&prod_vec);

        assert_eq!(sum_vec.len(), self.m);

        for &sum in sum_vec.iter() {
            if sum != F::ZERO {
                return false;
            }
        }

        true
    }
}

pub fn hadamard_product<F: Field + From<u64> + Hash>(vec1: &[F], vec2: &[F]) -> Vec<F> {
    assert_eq!(vec1.len(), vec2.len());
    vec1.iter()
        .zip(vec2.iter())
        .map(|(&v1, &v2)| v1 * v2)
        .collect()
}

pub fn vec_add<F: Field + From<u64> + Hash>(vec: &[Vec<F>]) -> Vec<F> {
    assert!(vec.len() > 1);
    vec.iter().fold(vec![F::ZERO; vec[0].len()], |acc, vec| {
        acc.iter().zip(vec.iter()).map(|(&a, &v)| a + v).collect()
    })
}

#[derive(Debug, Clone)]
pub struct Matrix<F> {
    n: usize,
    m: usize,
    values: Vec<Vec<F>>,
}

impl<F: Field> Matrix<F> {
    pub fn new(n: usize, m: usize) -> Self {
        Self {
            n,
            m,
            values: vec![vec![F::ZERO; n]; m],
        }
    }

    pub fn write(&mut self, values: &[(usize, usize, F)]) {
        for &(row, col, value) in values.iter() {
            assert!(row < self.m);
            assert!(col < self.n);
            self.values[row][col] = value;
        }
    }

    pub fn get(&self, row: usize, col: usize) -> F {
        assert!(row < self.m);
        assert!(col < self.n);
        self.values[row][col]
    }

    pub fn remove_rows(&mut self, m: usize) {
        assert!(m <= self.m);
        self.values = self.values[0..m].to_owned();
        self.m = m;
    }

    pub fn size(&self) -> (usize, usize) {
        (self.m, self.n)
    }

    pub fn values(&self) -> Vec<Vec<F>> {
        self.values.clone()
    }
}

impl<F: Field + From<u64> + Hash> Matrix<F> {
    pub fn matrix_vector_product(&self, z: &[F]) -> Vec<F> {
        (0..self.values.len())
            .map(|i| self.hadamard_product_and_sum(i, z))
            .collect()
    }

    fn hadamard_product_and_sum(&self, index: usize, z: &[F]) -> F {
        assert!(index < self.values.len());
        assert_eq!(self.values[index].len(), z.len());
        hadamard_product(&self.values[index], z).iter().sum()
    }
}

// input vector z = [1, x, w]
pub struct Z<F: Field + From<u64>> {
    pub n: usize,
    pub l: usize,
    pub assignments: Vec<F>,
    pub public_inputs: Vec<F>,
}

impl<F: Field + From<u64> + Hash> Z<F> {
    pub fn new(n: usize, l: usize) -> Self {
        assert!(n > l);
        Self {
            n,
            l,
            assignments: Default::default(),
            public_inputs: Default::default(),
        }
    }

    pub fn write(
        &mut self,
        inputs: &HashMap<(usize, UUID), F>,
        witnesses: &[HashMap<UUID, F>],
        witness_pos: &PositionMap,
        public_pos: &PositionMap,
    ) {
        assert_eq!(inputs.len(), self.l);

        let mut witness_values = vec![F::ZERO; witness_pos.len() - 1];
        for ((step_idx, signal_id), idx) in witness_pos.iter() {
            if *signal_id == 0 {
                continue;
            }
            witness_values[idx - 1] = *witnesses[*step_idx].get(signal_id).unwrap();
        }
        let mut public_values = vec![F::ZERO; public_pos.len()];
        for (pos, idx) in public_pos.iter() {
            public_values[idx - witness_pos.len()] = *inputs.get(pos).unwrap();
        }
        self.assignments = witness_values.clone();
        self.public_inputs = public_values.clone();
    }

    pub fn write_with_values(&mut self, inputs: &[F], witnesses: &[F]) {
        assert_eq!(inputs.len(), self.l);
        assert_eq!(witnesses.len(), self.n - self.l - 1);

        self.public_inputs = inputs.to_owned().clone();
        self.assignments = witnesses.to_owned().clone();
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_ccs() {
        let n = 7;
        let m = 4;
        let t = 8;
        let q = 5;
        let l = 3;

        let mut ccs_circuit: CCSCircuit<Fr> = CCSCircuit::new(n, m, t, q, l, 0);
        let m0 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 3, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m1 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 4, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m2 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 5, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m3 = vec![(0, 0, Fr::ONE), (1, 0, Fr::ONE)];
        let m4 = vec![(2, 0, Fr::from(2))];
        let m5 = vec![(2, 0, Fr::from(2))];
        let m6 = vec![
            (0, 0, Fr::ONE.neg()),
            (1, 0, Fr::ONE.neg()),
            (2, 0, Fr::ONE.neg()),
        ];
        let m7 = vec![(0, 0, Fr::ZERO)];
        let matrics = vec![m0, m1, m2, m3, m4, m5, m6, m7];

        let selectors = vec![
            vec![(3, Fr::ONE), (0, Fr::ONE), (1, Fr::ONE)],
            vec![(4, Fr::ONE), (0, Fr::ONE)],
            vec![(5, Fr::ONE), (1, Fr::ONE)],
            vec![(6, Fr::ONE), (2, Fr::ONE)],
            vec![(7, Fr::ONE)],
        ];
        let constants: Vec<Fr> = vec![Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE];
        ccs_circuit.write(&matrics, &selectors, &constants);

        let mut z = Z::new(n, l);
        z.write_with_values(
            &[Fr::ZERO, Fr::ONE, Fr::from(2)],
            &[Fr::from(3), Fr::from(10), Fr::from(43)],
        );

        let result = ccs_circuit.is_satisfied(&z);

        println!("result = {}", result);
    }
}
