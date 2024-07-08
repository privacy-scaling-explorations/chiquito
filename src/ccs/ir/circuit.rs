use std::{collections::HashMap, hash::Hash};

use super::{assignments::*, CoeffsForProds};
use crate::{
    ccs::compiler::step_selector::{SelectorsForALLMatrix, SelectorsForALLSteps, StepSelector},
    field::Field,
    util::UUID,
};

pub type MatrixCoeffsAndOffset<F> = Vec<Vec<(CoeffsForProds<F>, usize)>>;
pub type SelectorsOffsetAndCoeff<F> = Vec<Vec<(usize, F)>>;
#[derive(Debug)]
pub struct Circuit<F> {
    pub ast_id: UUID,

    pub matrix_coeffs_and_offsets: HashMap<UUID, MatrixCoeffsAndOffset<F>>,
    pub selectors: SelectorsOffsetAndCoeff<F>,
    pub constants: Vec<F>,
    pub exposed: Vec<(usize, UUID)>,
    pub witness: HashMap<UUID, Vec<UUID>>,

    pub d: usize,
    pub q: usize,
    pub t: usize,
}

impl<F: Field + From<u64> + Hash> Circuit<F> {
    pub fn new(ast_id: UUID) -> Self {
        Self {
            t: 0,
            q: 0,
            d: 0,
            matrix_coeffs_and_offsets: HashMap::new(),
            selectors: Vec::new(),
            constants: Vec::new(),
            exposed: Vec::new(),
            witness: HashMap::new(),
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

        self.constants = vec![F::ONE; self.q];
        self.selectors = selectors.matrix_selectors.clone();
        self.exposed = exposed.to_owned();
        self.witness = witness.clone();

        self.construct_matrix_coeffs_and_offsets(matrix_coeffs, &selectors.step_selectors);
    }

    fn calcu_bounds(&mut self, matrix_selectors: &SelectorsForALLMatrix<F>) {
        let mut t = 0;
        let mut d = 0;
        self.q = matrix_selectors.len();

        for selectors in matrix_selectors.iter() {
            d = d.max(selectors.len());
            for (idx, _) in selectors.iter() {
                t = t.max(*idx + 1);
            }
        }
        self.t = t;
        self.d = d;
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

    pub fn instance(&self, assignments: &Assignments<F>) -> HashMap<(usize, UUID), F> {
        let mut exposes = HashMap::new();
        for (step_idx, id) in self.exposed.iter() {
            exposes.insert((*step_idx, *id), assignments.get(*step_idx, *id));
        }
        exposes
    }
}
