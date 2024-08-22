use std::{collections::HashMap, hash::Hash};

use super::{assignments::*, CoeffsForProds};
use crate::{
    ccs::compiler::step_selector::{SelectorsForALLMatrix, SelectorsForALLSteps, StepSelector},
    field::Field,
    util::UUID,
};

pub type MatrixCoeffsAndOffset<F> = Vec<Vec<(CoeffsForProds<F>, usize)>>;
pub type SelectorsOffsetAndCoeff<F> = Vec<Vec<(usize, F)>>;

// ((step_idx, step_UUID), assignment_offset)
pub type AssignmentOffsets = HashMap<(usize, u128), usize>;

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
        witnesses: &[(UUID, HashMap<UUID, F>)],
        assign_pos: &AssignmentOffsets,
    ) {
        assert_eq!(inputs.len(), self.l);
        assert_eq!(assign_pos.len(), self.n);
        let witness_len = self.n - self.l - 1;
        let mut witness_values = vec![F::ZERO; witness_len];
        let mut public_values = vec![F::ZERO; self.l];
        for ((step_idx, signal_id), idx) in assign_pos.iter() {
            if *signal_id == 0 {
                continue;
            }
            if *idx < self.n - self.l {
                witness_values[*idx - 1] = *witnesses[*step_idx].1.get(signal_id).unwrap();
            } else {
                public_values[*idx - witness_len - 1] =
                    *inputs.get(&(*step_idx, *signal_id)).unwrap();
            }
        }
        self.assignments = witness_values;
        self.public_inputs = public_values;
    }

    pub fn write_with_values(&mut self, inputs: &[F], witnesses: &[F]) {
        assert_eq!(inputs.len(), self.l);
        assert_eq!(witnesses.len(), self.n - self.l - 1);

        self.public_inputs = inputs.to_owned().clone();
        self.assignments = witnesses.to_owned().clone();
    }
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

    pub fn reduce_rows(&mut self, m: usize) {
        if m < self.m {
            self.values = self.values[0..m].to_owned();
            self.m = m;
        }
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

#[derive(Debug, Default)]
pub struct CCSCircuit<F> {
    pub n: usize,
    pub m: usize,
    pub l: usize,
    pub t: usize,
    pub q: usize,
    pub d: usize,
    pub matrices: Vec<Matrix<F>>,
    pub selectors: SelectorsOffsetAndCoeff<F>,
    pub constants: Vec<F>,
}

impl<F: Field + From<u64> + Hash> CCSCircuit<F> {
    pub fn new() -> Self {
        let matrices = Vec::new();
        let selectors = Vec::new();
        let constants = Vec::new();

        Self {
            n: 0,
            m: 0,
            l: 0,
            t: 0,
            q: 0,
            d: 0,
            matrices,
            selectors,
            constants,
        }
    }

    pub fn public_num(&self) -> usize {
        self.l
    }

    pub fn witness_num(&self) -> usize {
        self.n - self.l - 1
    }

    pub fn write(
        &mut self,
        matrices: &[Vec<(usize, usize, F)>],
        selectors: &[Vec<(usize, F)>],
        constants: &[F],
    ) {
        self.write_constants(constants);
        self.write_selectors_and_degree(selectors);
        self.write_matrices(matrices);
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

    fn write_matrices(&mut self, matrices: &[Vec<(usize, usize, F)>]) {
        assert_eq!(matrices.len(), self.t);

        self.matrices = matrices
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
                        assert!(s < self.matrices.len());
                        self.matrices[s].matrix_vector_product(&values)
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

#[derive(Debug)]
pub struct Circuit<F> {
    pub ast_id: UUID,

    pub matrix_coeffs_and_offsets: HashMap<UUID, MatrixCoeffsAndOffset<F>>,
    pub exposed: Vec<(usize, UUID)>,
    pub witness: HashMap<UUID, Vec<UUID>>,

    pub ccs: CCSCircuit<F>,
}

impl<F: Field + From<u64> + Hash> Circuit<F> {
    pub fn new(ast_id: UUID) -> Self {
        Self {
            matrix_coeffs_and_offsets: HashMap::new(),
            exposed: Vec::new(),
            witness: HashMap::new(),
            ccs: CCSCircuit::new(),
            ast_id,
        }
    }

    pub fn write(
        &mut self,
        matrix_coeffs: &HashMap<UUID, Coeffs<F>>,
        selectors: &StepSelector<F>,
        exposed: &[(usize, UUID)],
        witness: &HashMap<UUID, Vec<UUID>>,
    ) {
        self.calcu_bounds(&selectors.matrix_selectors);

        self.ccs.constants = vec![F::ONE; self.ccs.q];
        self.ccs.selectors = selectors.matrix_selectors.clone();
        self.exposed = exposed.to_owned();
        self.witness = witness.clone();

        self.construct_matrix_coeffs_and_offsets(matrix_coeffs, &selectors.step_selectors);
    }

    fn calcu_bounds(&mut self, matrix_selectors: &SelectorsForALLMatrix<F>) {
        let mut t = 0;
        let mut d = 0;
        self.ccs.q = matrix_selectors.len();

        for selectors in matrix_selectors.iter() {
            d = d.max(selectors.len());
            for (idx, _) in selectors.iter() {
                t = t.max(*idx + 1);
            }
        }
        self.ccs.t = t;
        self.ccs.d = d;
    }

    fn construct_matrix_coeffs_and_offsets(
        &mut self,
        matrix_coeffs: &HashMap<UUID, Coeffs<F>>,
        step_selectors: &SelectorsForALLSteps,
    ) {
        let mut matrix_coeffs_and_offsets = HashMap::new();
        for (step_id, coeffs_one_step) in matrix_coeffs.iter() {
            let selectors_one_step = step_selectors.get(step_id).unwrap();
            let v = coeffs_one_step
                .iter()
                .zip(selectors_one_step.iter())
                .map(|(coeffs_one_poly, selectors_one_poly)| {
                    coeffs_one_poly
                        .iter()
                        .zip(selectors_one_poly.iter())
                        .map(|(coeffs_one_chunk, selectors_one_chunk)| {
                            (coeffs_one_chunk.clone(), *selectors_one_chunk)
                        })
                        .collect()
                })
                .collect();

            matrix_coeffs_and_offsets.insert(*step_id, v);
        }
        self.matrix_coeffs_and_offsets = matrix_coeffs_and_offsets;
    }

    pub fn instance(&self, assignments: &Option<Assignments<F>>) -> HashMap<(usize, UUID), F> {
        let mut exposes = HashMap::new();
        if !self.exposed.is_empty() {
            for (step_idx, id) in self.exposed.iter() {
                if let Some(witness) = assignments {
                    exposes.insert((*step_idx, *id), witness.get(*step_idx, *id));
                }
            }
        }
        exposes
    }

    pub fn generate(&mut self, assignments: Option<Assignments<F>>) -> Z<F> {
        let (assign_pos, n, l) = self.assignments_coeff_offset(&assignments);
        let matrix_num = calc_matrix_num(&self.ccs.selectors);

        let (matrices, m) = self.export_matrix_vec(&assignments, n, matrix_num, &assign_pos);

        self.ccs.n = n;
        self.ccs.l = l;
        self.ccs.m = m;
        self.ccs.matrices = matrices;

        let mut z: Z<F> = Z::new(n, l);
        z.write(
            &self.instance(&assignments),
            assignments.as_deref().unwrap(),
            &assign_pos,
        );

        z
    }

    fn assignments_coeff_offset(
        &self,
        witness: &Option<Assignments<F>>,
    ) -> (AssignmentOffsets, usize, usize) {
        let mut public_pos = HashMap::new();
        for (offset, (step_idx, signal_uuid)) in self.exposed.iter().enumerate() {
            public_pos.insert((*step_idx, *signal_uuid), offset);
        }

        let mut witness_pos = HashMap::new();
        let mut offset = 0;
        witness_pos.insert((0, 0), offset);
        offset += 1;
        if let Some(assignments) = witness.as_ref() {
            for (step_idx, (step_id, _)) in assignments.iter().enumerate() {
                let signal_uuids = self.witness.get(step_id).unwrap();
                for id in signal_uuids.iter() {
                    let exist = public_pos.get(&(step_idx, *id));
                    if exist.is_none() {
                        witness_pos.insert((step_idx, *id), offset);
                        offset += 1;
                    }
                }
            }
        }

        for ((step_idx, id), v) in public_pos.iter() {
            witness_pos.insert((*step_idx, *id), v + offset);
            offset += 1;
        }
        (witness_pos, offset, public_pos.len())
    }

    fn export_matrix_vec(
        &self,
        witness: &Option<Assignments<F>>,
        n: usize,
        num: usize,
        assign_pos: &AssignmentOffsets,
    ) -> (Vec<Matrix<F>>, usize) {
        let num_poly = witness
            .as_ref()
            .map(|steps_idx| {
                steps_idx
                    .iter()
                    .map(|(idx, _)| self.matrix_coeffs_and_offsets.get(idx).unwrap().len())
                    .sum()
            })
            .unwrap();
        let mut matrices = vec![Matrix::new(n, num_poly); num];
        let mut row = 0;

        if let Some(steps_id) = witness.as_ref() {
            let step_num = steps_id.len();
            for (step_idx, (step_id, _)) in steps_id.iter().enumerate() {
                for coeffs_one_poly in self.matrix_coeffs_and_offsets.get(step_id).unwrap().iter() {
                    if is_last_step_with_next_signal(coeffs_one_poly, step_num, step_idx) {
                        continue;
                    }

                    for (coeffs_chunks, index) in coeffs_one_poly.iter() {
                        assert!(*index <= self.ccs.selectors.len());
                        let selectors = self.ccs.selectors[*index].clone();
                        assert_eq!(coeffs_chunks.len(), selectors.len());

                        for (coeffs, (selector, _)) in coeffs_chunks.iter().zip(selectors.iter()) {
                            // one row in a matrix
                            let mut values: Vec<(usize, usize, F)> = Vec::new();
                            for (value, signal_id, next) in coeffs.iter() {
                                let col = if *signal_id == 0 {
                                    assign_pos.get(&(0, 0))
                                } else {
                                    let idx = if *next { step_idx + 1 } else { step_idx };
                                    assign_pos.get(&(idx, *signal_id))
                                };
                                match col {
                                    None => continue,
                                    Some(col) => values.push((row, *col, *value)),
                                }
                            }
                            matrices[*selector].write(&values);
                        }
                    }
                    row += 1;
                }
            }
        };

        for matrix in matrices.iter_mut() {
            matrix.reduce_rows(row);
        }
        (matrices, row)
    }
}

fn calc_matrix_num<F>(selectors: &SelectorsOffsetAndCoeff<F>) -> usize {
    let mut matrix_num = 0;
    for selector in selectors.iter() {
        for (idx, _) in selector.iter() {
            matrix_num = matrix_num.max(*idx + 1);
        }
    }
    matrix_num
}

fn is_last_step_with_next_signal<F: Clone>(
    coeffs_one_poly: &[(CoeffsForProds<F>, usize)],
    step_num: usize,
    step_idx: usize,
) -> bool {
    if step_idx == step_num - 1 {
        for (coeffs_for_prods, _) in coeffs_one_poly.iter() {
            for (_, _, next) in coeffs_for_prods.concat().iter() {
                if *next {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_ccs() {
        let n = 7;
        let l = 3;

        let mut ccs_circuit: CCSCircuit<Fr> = CCSCircuit::new();
        ccs_circuit.n = n;
        ccs_circuit.m = 4;
        ccs_circuit.t = 8;
        ccs_circuit.q = 5;
        ccs_circuit.l = 3;

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
