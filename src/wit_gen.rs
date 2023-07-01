use std::{collections::HashMap, hash::Hash, rc::Rc};

use crate::{
    ast::{query::Queriable, StepTypeUUID},
    dsl::StepTypeWGHandler,
};

/// A struct that represents a witness generation context. It provides an interface for assigning
/// values to witness columns in a circuit.
#[derive(Debug, Default)]
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

impl<F: Eq + Hash> StepInstance<F> {
    /// Takes a `Queriable` object representing the witness column (lhs) and the value (rhs) to be
    /// assigned.
    pub fn assign(&mut self, lhs: Queriable<F>, rhs: F) {
        self.assignments.insert(lhs, rhs);
    }
}

pub type Witness<F> = Vec<StepInstance<F>>;

#[derive(Debug, Default)]
pub struct TraceWitness<F> {
    pub step_instances: Witness<F>,
    pub height: usize,
}

#[derive(Debug, Default)]
pub struct TraceContext<F> {
    witness: TraceWitness<F>,
}

impl<F> TraceContext<F> {
    pub fn get_witness(self) -> TraceWitness<F> {
        self.witness
    }
}

impl<F> TraceContext<F> {
    pub fn add<Args, WG: Fn(&mut StepInstance<F>, Args) + 'static>(
        &mut self,
        step: &StepTypeWGHandler<F, Args, WG>,
        args: Args,
    ) {
        let mut witness = StepInstance::new(step.uuid());

        (*step.wg)(&mut witness, args);

        self.witness.step_instances.push(witness);
    }

    pub fn set_height(&mut self, height: usize) {
        self.witness.height = height;
    }
}

pub type Trace<F, TraceArgs> = dyn Fn(&mut TraceContext<F>, TraceArgs) + 'static;

#[derive(Clone)]
pub struct TraceGenerator<F, TraceArgs> {
    trace: Rc<Trace<F, TraceArgs>>,
}

impl<F: Default, TraceArgs> TraceGenerator<F, TraceArgs> {
    pub fn new(trace: Rc<Trace<F, TraceArgs>>) -> Self {
        Self { trace }
    }

    pub fn generate(&self, args: TraceArgs) -> TraceWitness<F> {
        let mut ctx = TraceContext::default();

        (self.trace)(&mut ctx, args);

        ctx.get_witness()
    }
}
