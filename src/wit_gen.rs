use std::{collections::HashMap, hash::Hash, rc::Rc};

use crate::{
    ast::{query::Queriable, StepType, StepTypeUUID},
    compiler::{TraceContext, WitnessGenContext},
    dsl::StepTypeHandler,
};

pub struct StepInstance<F> {
    pub step_type_uuid: StepTypeUUID,
    pub assignments: HashMap<Queriable<F>, F>,
}

impl<F> StepInstance<F> {
    pub fn new(step_type_uuid: StepTypeUUID) -> StepInstance<F> {
        StepInstance {
            step_type_uuid,
            assignments: HashMap::default(),
        }
    }
}

impl<F: Eq + Hash> WitnessGenContext<F> for StepInstance<F> {
    fn assign(&mut self, lhs: Queriable<F>, rhs: F) {
        self.assignments.insert(lhs, rhs);
    }
}

pub type Witness<F> = Vec<StepInstance<F>>;

pub struct TraceWitness<F> {
    pub step_instances: Witness<F>,
    pub height: usize,
}

impl<F> Default for TraceWitness<F> {
    fn default() -> Self {
        Self {
            step_instances: Default::default(),
            height: Default::default(),
        }
    }
}

pub struct GenericTraceContext<'a, F, StepArgs> {
    step_types: &'a HashMap<u32, Rc<StepType<F, StepArgs>>>,

    witness: TraceWitness<F>,
}

impl<'a, F, StepArgs> GenericTraceContext<'a, F, StepArgs> {
    pub fn new(step_types: &'a HashMap<u32, Rc<StepType<F, StepArgs>>>) -> Self {
        Self {
            step_types,
            witness: TraceWitness::default(),
        }
    }

    pub fn get_witness(self) -> TraceWitness<F> {
        self.witness
    }
}

impl<'a, F: Eq + Hash, StepArgs> TraceContext<StepArgs> for GenericTraceContext<'a, F, StepArgs> {
    fn add(&mut self, step: &StepTypeHandler, args: StepArgs) {
        let step = Rc::clone(
            self.step_types
                .get(&step.uuid())
                .expect("step type not found"),
        );

        let mut witness = StepInstance::new(step.uuid());

        (*step.wg)(&mut witness, args);

        self.witness.step_instances.push(witness);
    }

    fn set_height(&mut self, height: usize) {
        self.witness.height = height;
    }
}
