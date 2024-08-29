use crate::{
    ccs::ir::{
        assignments::{Assignments, Coeffs, Z},
        circuit::{CCSCircuit, Matrix, SelectorsOffsetAndCoeff},
        AssignmentOffsets, Circuit, CoeffsForProds, CoeffsForSteps, Poly,
    },
    field::Field,
    sbpir::{FixedSignal, ForwardSignal, SharedSignal, StepType, SBPIR as astCircuit},
    util::{uuid, UUID},
};

use std::{collections::HashMap, hash::Hash, rc::Rc};

use super::{
    cell_manager::{Placement, SignalPlacement},
    step_selector::{SelectorsForALLMatrix, SelectorsForALLSteps, StepSelector},
};

#[derive(Debug, Clone)]
pub struct CompilationUnit<F> {
    pub ast_id: UUID,
    pub uuid: UUID,
    pub annotations: HashMap<UUID, String>,

    pub placement: Placement,
    pub forward_signals: Vec<ForwardSignal>,
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,

    pub num_steps: usize,
    pub step_types: HashMap<UUID, Rc<StepType<F>>>,

    pub exposed: Vec<(usize, SignalPlacement)>,

    pub polys: HashMap<UUID, Vec<Poly<F>>>,
    pub selector: StepSelector<F>,
    pub matrix_coeffs: CoeffsForSteps<F>,
}

impl<F> Default for CompilationUnit<F> {
    fn default() -> Self {
        Self {
            ast_id: Default::default(),
            uuid: uuid(),
            step_types: Default::default(),
            forward_signals: Default::default(),
            shared_signals: Default::default(),
            fixed_signals: Default::default(),
            annotations: Default::default(),
            exposed: Default::default(),
            num_steps: Default::default(),
            selector: Default::default(),
            polys: Default::default(),
            placement: Default::default(),
            matrix_coeffs: Default::default(),
        }
    }
}

impl<F, TraceArgs> From<&astCircuit<F, TraceArgs>> for CompilationUnit<F> {
    fn from(ast: &astCircuit<F, TraceArgs>) -> Self {
        Self {
            ast_id: ast.id,
            uuid: uuid(),
            annotations: {
                let mut acc = ast.annotations.clone();
                for step in ast.step_types.values() {
                    acc.extend(step.annotations.clone());
                }

                acc
            },
            step_types: ast.step_types.clone(),
            forward_signals: ast.forward_signals.clone(),
            shared_signals: ast.shared_signals.clone(),
            fixed_signals: ast.fixed_signals.clone(),
            num_steps: ast.num_steps,

            ..Default::default()
        }
    }
}

impl<F: Field + Hash> From<CompilationUnit<F>> for Circuit<F> {
    fn from(unit: CompilationUnit<F>) -> Self {
        let exposed: Vec<(usize, UUID)> = unit
            .exposed
            .iter()
            .map(|(step, exposed)| (*step, exposed.uuid()))
            .collect();

        let mut witnesses = HashMap::new();
        for (step_uuid, _) in unit.matrix_coeffs.iter() {
            let mut signal_uuids: Vec<UUID> = unit.placement.forward.keys().copied().collect();
            signal_uuids.append(&mut unit.placement.shared.keys().copied().collect());
            signal_uuids.append(&mut unit.placement.fixed.keys().copied().collect());
            signal_uuids.append(
                &mut unit
                    .placement
                    .step(*step_uuid)
                    .signals()
                    .keys()
                    .copied()
                    .collect(),
            );
            witnesses.insert(*step_uuid, signal_uuids);
        }

        let mut circuit = Circuit::new(unit.ast_id);
        circuit.write(&unit.matrix_coeffs, &unit.selector, &exposed, &witnesses);

        circuit
    }
}

impl<F: Field + From<u64> + Hash> Circuit<F> {
    pub fn new(ast_id: UUID) -> Self {
        Self {
            matrix_coeffs_and_offsets: HashMap::new(),
            exposed: Vec::new(),
            witness: HashMap::new(),
            ccs: CCSCircuit::default(),
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
        self.ccs.selectors.clone_from(&selectors.matrix_selectors);
        exposed.clone_into(&mut self.exposed);
        self.witness.clone_from(witness);

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

    pub fn generate(&mut self, assignments: Option<Assignments<F>>) -> Z<F> {
        let (assign_pos, n, l) = self.assignments_coeff_offset(&assignments);
        let matrix_num = calc_matrix_num(&self.ccs.selectors);

        let (matrices, m) = self.export_matrix_vec(&assignments, n, matrix_num, &assign_pos);

        self.ccs.n = n;
        self.ccs.l = l;
        self.ccs.m = m;
        self.ccs.matrices = matrices;

        create_z_from_assignments(&assignments, &self.instance(&assignments), &assign_pos)
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
        // Initial a vector of Matrices
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
                            // Modify matrices values from steps
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

pub fn create_z_from_assignments<F: Field + From<u64> + Hash>(
    assignments: &Option<Assignments<F>>,
    inputs: &HashMap<(usize, UUID), F>,
    assign_pos: &AssignmentOffsets,
) -> Z<F> {
    let l = inputs.len();
    let n = assign_pos.len();
    let mut z = Z::new(n, l);

    let witnesses = assignments.as_deref().unwrap();

    let witness_len = n - l - 1;
    let mut witness_values = vec![F::ZERO; witness_len];
    let mut public_values = vec![F::ZERO; l];
    for ((step_idx, signal_id), idx) in assign_pos.iter() {
        if *signal_id == 0 {
            continue;
        }
        if *idx < n - l {
            witness_values[*idx - 1] = *witnesses[*step_idx].1.get(signal_id).unwrap();
        } else {
            public_values[*idx - witness_len - 1] = *inputs.get(&(*step_idx, *signal_id)).unwrap();
        }
    }
    z.witnesses = witness_values;
    z.public_inputs = public_values;

    z
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
