use crate::{field::Field, util::UUID};

use super::{CompilationUnit, PolyExpr};
use std::collections::HashMap;

pub type SelectorAssignment<F> = (PolyExpr<F>, F);

pub type SelectorForMatrix<F> = (usize, F);
pub type SelectorForProd<F> = Vec<SelectorForMatrix<F>>;
pub type SelectorsForALLMatrix<F> = Vec<SelectorForProd<F>>;

pub type SelectorsForPoly = Vec<usize>;
pub type SelectorsForOneStep = Vec<SelectorsForPoly>;
pub type SelectorsForALLSteps = HashMap<UUID, SelectorsForOneStep>;

#[derive(Debug, Clone)]
pub struct StepSelector<F> {
    pub matrix_selectors: SelectorsForALLMatrix<F>,
    pub step_selectors: SelectorsForALLSteps,
}

impl<F> Default for StepSelector<F> {
    fn default() -> Self {
        Self {
            step_selectors: Default::default(),
            matrix_selectors: Default::default(),
        }
    }
}

pub trait StepSelectorBuilder: Clone {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>);
}

#[derive(Debug, Default, Clone)]
pub struct SimpleStepSelectorBuilder {}

impl StepSelectorBuilder for SimpleStepSelectorBuilder {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>) {
        let mut matrix_selectors: SelectorsForALLMatrix<F> = Vec::new();
        let mut step_selectors: SelectorsForALLSteps = HashMap::new();

        let mut matrix_num = 0;

        for (step_id, coeffs_one_step) in unit.matrix_coeffs.iter() {
            let selectors_one_step = coeffs_one_step
                .iter()
                .map(|coeffs_one_poly| {
                    let mut used = vec![false; matrix_selectors.len()];
                    coeffs_one_poly
                        .iter()
                        .map(|coeffs_prods| {
                            let size = coeffs_prods.len();
                            let mut offset = matrix_selectors.len();
                            for (i, prods_selector) in matrix_selectors.iter().enumerate() {
                                if prods_selector.len() == size && !used[i] {
                                    used[i] = true;
                                    offset = i;
                                    break;
                                }
                            }
                            if offset == matrix_selectors.len() {
                                matrix_selectors.push(
                                    (matrix_num..size + matrix_num)
                                        .map(|i| (i, F::ONE))
                                        .collect(),
                                );
                                matrix_num += size;
                                used.push(true);
                            }
                            offset
                        })
                        .collect()
                })
                .collect();

            step_selectors.insert(*step_id, selectors_one_step);
        }

        unit.selector = StepSelector {
            step_selectors,
            matrix_selectors,
        };
    }
}
