use std::{collections::HashMap, hash::Hash};

use super::assignments::*;
use crate::{ccs::compiler::step_selector::StepSelector, field::Field, util::UUID};

#[derive(Debug)]
pub struct Circuit<F> {
    pub ast_id: UUID,

    pub matrics: HashMap<UUID, MatrixsCoeffs<F>>,
    pub selectors: Vec<Vec<(usize, F)>>,
    pub constants: Vec<F>,
    pub exposed: Vec<(usize, UUID)>,
    pub witness: HashMap<UUID, Vec<UUID>>,

    pub d: usize,
    pub q: usize,
    pub t: usize,
}

impl<F: Field + From<u64> + Hash> Circuit<F> {
    pub fn new(ast_id: UUID) -> Self {
        let matrics = HashMap::new();
        let selectors = Vec::new();
        let constants = Vec::new();
        let exposed = vec![];
        let witness = HashMap::new();

        Self {
            t: 0,
            q: 0,
            d: 0,
            matrics,
            selectors,
            constants,
            exposed,
            witness,
            ast_id,
        }
    }

    pub fn write(
        &mut self,
        matrix_values: &HashMap<UUID, Coeffs<F>>,
        selectors: &StepSelector<F>,
        exposed: &[(usize, UUID)],
        witness: &HashMap<UUID, Vec<UUID>>,
    ) {
        let mut t = 0;
        let mut d = 0;

        self.q = selectors.matrix_selectors.len();
        self.constants = vec![F::ONE; self.q];

        for selectors in selectors.matrix_selectors.iter() {
            d = d.max(selectors.len());
            for (selector, _) in selectors.iter() {
                t = t.max(*selector);
            }
        }
        self.selectors = selectors.matrix_selectors.clone();

        let mut matrics = HashMap::new();
        for (uuid, values) in matrix_values.iter() {
            let selectors = selectors.step_selectors.get(uuid).unwrap();
            let v = values
                .iter()
                .zip(selectors.iter())
                .map(|(values, selectors)| {
                    values
                        .iter()
                        .zip(selectors.iter())
                        .map(|(values, selectors)| (values.clone(), *selectors))
                        .collect()
                })
                .collect();

            matrics.insert(*uuid, v);
        }
        self.matrics = matrics;
        self.exposed = exposed.to_owned();
        self.witness = witness.clone();
        self.selectors = selectors.matrix_selectors.clone();
    }

    pub fn instance(&self, assignments: &Assignments<F>) -> HashMap<(usize, UUID), F> {
        let mut exposes = HashMap::new();
        for (step_idx, id) in self.exposed.iter() {
            exposes.insert((*step_idx, *id), assignments.get(*step_idx, *id));
        }
        exposes
    }
}
