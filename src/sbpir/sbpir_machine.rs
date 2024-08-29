use crate::{
    field::Field,
    frontend::dsl::{
        trace::{DSLTraceGenerator, TraceContext},
        StepTypeHandler,
    },
    poly::Expr,
    sbpir::Halo2Column,
    util::{uuid, UUID},
    wit_gen::{FixedAssignment, NullTraceGenerator, TraceGenerator},
};
use halo2_proofs::plonk::{Advice, Fixed};
use std::{collections::HashMap, fmt::Debug, hash::Hash, rc::Rc};

use super::{
    query::Queriable, ExposeOffset, FixedSignal, ForwardSignal, ImportedHalo2Advice,
    ImportedHalo2Fixed, SharedSignal, StepType, StepTypeUUID,
};

/// Step-Based Polynomial Identity Representation (SBPIR) of a single machine.
#[derive(Clone)]
pub struct SBPIRMachine<F: Clone, TG: TraceGenerator<F> = DSLTraceGenerator<F>, M: Clone = ()> {
    pub step_types: HashMap<UUID, StepType<F, M>>,

    pub forward_signals: Vec<ForwardSignal>,
    // TODO currently not used
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,
    pub halo2_advice: Vec<ImportedHalo2Advice>,
    pub halo2_fixed: Vec<ImportedHalo2Fixed>,
    pub exposed: Vec<(Queriable<F>, ExposeOffset)>,

    pub annotations: HashMap<UUID, String>,

    pub trace_generator: Option<TG>,
    // TODO currently not used
    pub fixed_assignments: Option<FixedAssignment<F>>,

    pub first_step: Option<StepTypeUUID>,
    pub last_step: Option<StepTypeUUID>,
    pub num_steps: usize,
    pub q_enable: bool,

    pub id: UUID,
}

impl<F: Debug + Clone, TG: TraceGenerator<F>, M: Debug + Clone> Debug for SBPIRMachine<F, TG, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Circuit")
            .field("step_types", &self.step_types)
            .field("forward_signals", &self.forward_signals)
            .field("shared_signals", &self.shared_signals)
            .field("fixed_signals", &self.fixed_signals)
            .field("halo2_advice", &self.halo2_advice)
            .field("halo2_fixed", &self.halo2_fixed)
            .field("exposed", &self.exposed)
            .field("annotations", &self.annotations)
            .field("fixed_assignments", &self.fixed_assignments)
            .field("first_step", &self.first_step)
            .field("last_step", &self.last_step)
            .field("num_steps", &self.num_steps)
            .field("q_enable", &self.q_enable)
            .finish()
    }
}

impl<F: Clone, TG: TraceGenerator<F>, M: Clone> Default for SBPIRMachine<F, TG, M> {
    fn default() -> Self {
        Self {
            step_types: Default::default(),
            forward_signals: Default::default(),
            shared_signals: Default::default(),
            fixed_signals: Default::default(),
            halo2_advice: Default::default(),
            halo2_fixed: Default::default(),
            exposed: Default::default(),

            num_steps: Default::default(),

            annotations: Default::default(),

            trace_generator: None,
            fixed_assignments: None,

            first_step: None,
            last_step: None,

            id: uuid(),
            q_enable: true,
        }
    }
}

impl<F: Clone, TG: TraceGenerator<F>, M: Clone> SBPIRMachine<F, TG, M> {
    pub fn add_forward<N: Into<String>>(&mut self, name: N, phase: usize) -> ForwardSignal {
        let name = name.into();
        let signal = ForwardSignal::new_with_phase(phase, name.clone());

        self.forward_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    pub fn add_shared<N: Into<String>>(&mut self, name: N, phase: usize) -> SharedSignal {
        let name = name.into();
        let signal = SharedSignal::new_with_phase(phase, name.clone());

        self.shared_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    // TODO currently not used
    pub fn add_fixed<N: Into<String>>(&mut self, name: N) -> FixedSignal {
        let name = name.into();
        let signal = FixedSignal::new(name.clone());

        self.fixed_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    // TODO currently not used
    pub fn expose(&mut self, signal: Queriable<F>, offset: ExposeOffset) {
        match signal {
            Queriable::Forward(..) | Queriable::Shared(..) => {
                let existing_forward_signal = self
                    .forward_signals
                    .clone()
                    .iter()
                    .any(|s| s.uuid() == signal.uuid());
                let existing_shared_signal = self
                    .shared_signals
                    .clone()
                    .iter()
                    .any(|s| s.uuid() == signal.uuid());
                if !existing_forward_signal && !existing_shared_signal {
                    panic!("Signal not found in forward signals.");
                }
                self.exposed.push((signal, offset));
            }
            _ => panic!("Can only expose forward and shared signals."),
        }
    }

    pub fn add_halo2_advice(
        &mut self,
        name: &str,
        column: Halo2Column<Advice>,
    ) -> ImportedHalo2Advice {
        let advice = ImportedHalo2Advice::new(column, name.to_string());

        self.halo2_advice.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_halo2_fixed(
        &mut self,
        name: &str,
        column: Halo2Column<Fixed>,
    ) -> ImportedHalo2Fixed {
        let advice = ImportedHalo2Fixed::new(column, name.to_string());

        self.halo2_fixed.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_step_type<N: Into<String>>(&mut self, name: N) -> StepTypeHandler {
        let annotation = name.into();
        let handler = StepTypeHandler::new(annotation.clone());
        self.annotations.insert(handler.uuid(), annotation);
        handler
    }

    pub fn add_step_type_def(&mut self, step: StepType<F, M>) -> StepTypeUUID {
        let uuid = step.uuid();
        self.step_types.insert(uuid, step);

        uuid
    }

    pub fn set_fixed_assignments(&mut self, assignments: FixedAssignment<F>) {
        match self.fixed_assignments {
            None => {
                self.fixed_assignments = Some(assignments);
            }
            Some(_) => panic!("circuit cannot have more than one fixed generator"),
        }
    }

    pub fn without_trace(&self) -> SBPIRMachine<F, NullTraceGenerator, M> {
        SBPIRMachine {
            step_types: self.step_types.clone(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace_generator: None, // Remove the trace.
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }

    pub(crate) fn with_trace<TG2: TraceGenerator<F>>(&self, clone: TG2) -> SBPIRMachine<F, TG2, M> {
        SBPIRMachine {
            trace_generator: Some(clone), // Set trace
            step_types: self.step_types.clone(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

impl<F: Field, TraceArgs: Clone> SBPIRMachine<F, DSLTraceGenerator<F, TraceArgs>> {
    pub fn set_trace<D>(&mut self, def: D)
    where
        D: Fn(&mut TraceContext<F>, TraceArgs) + 'static,
    {
        // TODO: should we check that number of steps has been set?

        match self.trace_generator {
            None => {
                self.trace_generator = Some(DSLTraceGenerator::new(Rc::new(def), self.num_steps));
            }
            Some(_) => panic!("circuit cannot have more than one trace generator"),
        }
    }
}

impl<F: Clone + Field, TG: TraceGenerator<F>> SBPIRMachine<F, TG> {
    pub fn clone_without_trace(&self) -> SBPIRMachine<F, NullTraceGenerator> {
        SBPIRMachine {
            step_types: self.step_types.clone(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace_generator: None, // Remove the trace.
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

impl<F: Clone + PartialEq + Eq + Hash, TG: TraceGenerator<F> + Clone, M: Clone>
    SBPIRMachine<F, TG, M>
{
    pub fn transform_meta<N: Clone, ApplyMetaFn>(
        &self,
        apply_meta: ApplyMetaFn,
    ) -> SBPIRMachine<F, TG, N>
    where
        ApplyMetaFn: Fn(&Expr<F, Queriable<F>, M>) -> N + Clone,
    {
        SBPIRMachine {
            step_types: self
                .step_types
                .iter()
                .map(|(uuid, step_type)| (*uuid, step_type.transform_meta(apply_meta.clone())))
                .collect(),

            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),

            annotations: self.annotations.clone(),

            trace_generator: self.trace_generator.clone(),
            fixed_assignments: self.fixed_assignments.clone(),

            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,

            id: self.id,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::wit_gen::NullTraceGenerator;

    use super::*;

    #[test]
    fn test_q_enable() {
        let circuit: SBPIRMachine<i32, NullTraceGenerator> = SBPIRMachine::default();
        assert!(circuit.q_enable);
    }

    #[test]
    #[should_panic]
    fn test_expose_non_existing_signal() {
        let mut circuit: SBPIRMachine<i32, NullTraceGenerator> = SBPIRMachine::default();
        let signal = Queriable::Forward(
            ForwardSignal::new_with_phase(0, "signal".to_string()),
            false,
        );
        let offset = ExposeOffset::First;

        circuit.expose(signal, offset);
    }

    #[test]
    fn test_expose_forward_signal() {
        let mut circuit: SBPIRMachine<i32, NullTraceGenerator> = SBPIRMachine::default();
        let signal = circuit.add_forward("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Forward(signal, false), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }

    #[test]
    fn test_expose_shared_signal() {
        let mut circuit: SBPIRMachine<i32, NullTraceGenerator> = SBPIRMachine::default();
        let signal = circuit.add_shared("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Shared(signal, 10), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }
}