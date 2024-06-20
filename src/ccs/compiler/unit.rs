use crate::{
    ccs::{
        compiler::SignalPlacement,
        ir::{circuit::Circuit, CoeffsForSteps, Poly},
    },
    field::Field,
    sbpir::{FixedSignal, ForwardSignal, SharedSignal, StepType, SBPIR as astCircuit},
    util::{uuid, UUID},
};

use std::{collections::HashMap, hash::Hash, rc::Rc};

use super::{cell_manager::Placement, step_selector::StepSelector};

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
        let mut circuit = Circuit::new(unit.ast_id);

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

        circuit.write(&unit.matrix_coeffs, &unit.selector, &exposed, &witnesses);

        circuit
    }
}
