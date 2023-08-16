use core::fmt::Debug;
use std::{collections::HashMap, rc::Rc};

use halo2_proofs::plonk::{Advice, Column as Halo2Column};

use crate::{
    ast::{
        Circuit as astCircuit, FixedSignal, ForwardSignal, ImportedHalo2Advice, ImportedHalo2Fixed,
        SharedSignal, StepType, StepTypeUUID,
    },
    plonkish::ir::{assignments::Assignments, Circuit, Column, ColumnType, Poly, PolyLookup},
    util::{uuid, UUID},
};

use super::{
    cell_manager::{Placement, SignalPlacement},
    step_selector::StepSelector,
};

#[derive(Debug, Clone)]
pub struct CompilationUnit<F> {
    pub placement: Placement,
    pub selector: StepSelector<F>,
    pub step_types: HashMap<UUID, Rc<StepType<F>>>,
    pub forward_signals: Vec<ForwardSignal>,
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,

    pub annotations: HashMap<UUID, String>,

    pub columns: Vec<Column>,
    pub exposed: Vec<(Column, i32)>,

    pub num_steps: usize,
    pub q_enable: Option<Column>,
    pub first_step: Option<(StepTypeUUID, Column)>,
    pub last_step: Option<(Option<StepTypeUUID>, Column)>,

    pub num_rows: usize,

    pub polys: Vec<Poly<F>>,
    pub lookups: Vec<PolyLookup<F>>,

    pub fixed_assignments: Assignments<F>,

    pub ast_id: UUID,
    pub uuid: UUID,

    pub other_sub_circuits: Rc<Vec<CompilationUnit<F>>>,
    pub other_columns: Rc<Vec<Column>>,
}

impl<F> Default for CompilationUnit<F> {
    fn default() -> Self {
        Self {
            placement: Default::default(),
            selector: Default::default(),
            step_types: Default::default(),
            forward_signals: Default::default(),
            shared_signals: Default::default(),
            fixed_signals: Default::default(),

            annotations: Default::default(),

            columns: Default::default(),
            exposed: Default::default(),

            num_steps: Default::default(),
            q_enable: Default::default(),
            first_step: Default::default(),
            last_step: Default::default(),

            num_rows: Default::default(),

            polys: Default::default(),
            lookups: Default::default(),

            fixed_assignments: Default::default(),

            ast_id: Default::default(),
            uuid: uuid(),

            other_sub_circuits: Default::default(),
            other_columns: Default::default(),
        }
    }
}

impl<F> CompilationUnit<F> {
    pub(super) fn find_halo2_advice(&self, to_find: ImportedHalo2Advice) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_advice(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    pub(super) fn find_halo2_advice_native(&self, to_find: Halo2Column<Advice>) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice.column == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_advice_native(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    pub(super) fn find_halo2_fixed(&self, to_find: ImportedHalo2Fixed) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(fixed) = column.halo2_fixed {
                if fixed == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_fixed(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    pub fn get_forward_placement(&self, forward: &ForwardSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_forward_placement(forward) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(placement) = sub_circuit.placement.get_forward_placement(forward) {
                return placement;
            }
        }

        panic!("forward signal placement not found");
    }
    pub fn get_shared_placement(&self, shared: &SharedSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_shared_placement(shared) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(placement) = sub_circuit.placement.get_shared_placement(shared) {
                return placement;
            }
        }

        panic!("shared signal placement not found");
    }

    pub fn get_fixed_placement(&self, fixed: &FixedSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_fixed_placement(fixed) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(signal) = sub_circuit.placement.get_fixed_placement(fixed) {
                return signal;
            }
        }

        panic!("fixed signal placement not found");
    }

    fn has_transition_constraints<TraceArgs>(ast: &astCircuit<F, TraceArgs>) -> bool {
        for step in ast.step_types.values() {
            if !step.transition_constraints.is_empty() {
                return true;
            }
        }

        false
    }
}

impl<F, TraceArgs> From<&astCircuit<F, TraceArgs>> for CompilationUnit<F> {
    fn from(ast: &astCircuit<F, TraceArgs>) -> Self {
        CompilationUnit::<F> {
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
            q_enable: if ast.q_enable {
                Some(Column {
                    annotation: "q_enable".to_owned(),
                    ctype: ColumnType::Fixed,
                    halo2_advice: None,
                    halo2_fixed: None,
                    phase: 0,
                    id: uuid(),
                })
            } else {
                None
            },
            first_step: ast.first_step.map(|step_type_uuid| {
                (
                    step_type_uuid,
                    Column {
                        annotation: "q_first".to_owned(),
                        ctype: ColumnType::Fixed,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: uuid(),
                    },
                )
            }),
            last_step: if ast.last_step.is_some() || Self::has_transition_constraints(ast) {
                Some((
                    ast.last_step,
                    Column {
                        annotation: "q_last".to_owned(),
                        ctype: ColumnType::Fixed,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: uuid(),
                    },
                ))
            } else {
                None
            },
            ast_id: ast.id,
            ..Default::default()
        }
    }
}

impl<F> From<CompilationUnit<F>> for Circuit<F> {
    fn from(unit: CompilationUnit<F>) -> Self {
        Circuit::<F> {
            columns: unit.columns,
            exposed: unit.exposed,
            polys: unit.polys,
            lookups: unit.lookups,
            fixed_assignments: unit.fixed_assignments,
            id: unit.uuid,
            ast_id: unit.ast_id,
        }
    }
}
