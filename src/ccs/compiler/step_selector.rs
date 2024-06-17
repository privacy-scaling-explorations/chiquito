use crate::{ccs::ir::assignments::Coeffs, field::Field, util::UUID};

use super::{CompilationUnit, PolyExpr};
use std::collections::HashMap;

pub type SelectorAssignment<F> = (PolyExpr<F>, F);

#[derive(Debug, Clone)]
pub struct StepSelector<F> {
    pub matrix_selectors: Vec<Vec<(usize, F)>>,
    pub step_selectors: HashMap<UUID, Vec<Vec<usize>>>,
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
        let mut matrix_values = HashMap::new();
        for (step_id, polys) in unit.polys.iter() {
            // one step
            let values = polys
                .iter()
                .map(|poly| {
                    // one poly
                    poly.expr.poly_to_matrix(true)
                })
                .collect();
            matrix_values.insert(*step_id, values);
        }
        let mut matrix_selectors: Vec<Vec<(usize, F)>> = Vec::new();
        let mut step_selectors: HashMap<UUID, Vec<Vec<usize>>> = HashMap::new();
        construct_selector(&matrix_values, &mut matrix_selectors, &mut step_selectors);

        unit.selector = StepSelector {
            step_selectors,
            matrix_selectors,
        };
        unit.matrix_values = matrix_values;
    }
}

fn construct_selector<F: Field>(
    values: &HashMap<UUID, Coeffs<F>>,
    matrix_selectors: &mut Vec<Vec<(usize, F)>>,
    step_selectors: &mut HashMap<UUID, Vec<Vec<usize>>>,
) {
    let mut total = matrix_selectors.iter().map(|v| v.len()).sum();

    for (idx, polys_values) in values.iter() {
        let mut step_selector = Vec::new();
        for poly_values in polys_values.iter() {
            let mut constr_selector = Vec::new();
            let mut used = vec![false; matrix_selectors.len()];
            for chunk_values in poly_values.iter() {
                let size = chunk_values.len();
                let mut pos = matrix_selectors.len();
                for (i, matrix_selector) in matrix_selectors.iter().enumerate() {
                    if matrix_selector.len() == size && !used[i] {
                        pos = i;
                        used[pos] = true;
                        constr_selector.push(pos);
                        break;
                    }
                }
                if pos == matrix_selectors.len() {
                    matrix_selectors.push((total..size + total).map(|i| (i, F::ONE)).collect());
                    total += size;
                    used.push(true);
                    constr_selector.push(pos);
                }
            }
            step_selector.push(constr_selector);
        }

        step_selectors.insert(*idx, step_selector);
    }
}
