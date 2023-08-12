use std::{collections::HashMap, hash::Hash, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::{query::Queriable, StepTypeUUID},
    frontend::dsl::StepTypeWGHandler,
};

/// A struct that represents a witness generation context. It provides an interface for assigning
/// values to witness columns in a circuit.
#[derive(Debug, Default, Clone)]
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
}

#[derive(Debug)]
pub struct TraceContext<F> {
    witness: TraceWitness<F>,
    num_steps: usize,
}

impl<F: Default> TraceContext<F> {
    pub fn new(num_steps: usize) -> Self {
        Self {
            witness: TraceWitness::default(),
            num_steps,
        }
    }

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

    // This function pads the rest of the circuit with the given StepTypeWGHandler
    pub fn padding<Args, WG: Fn(&mut StepInstance<F>, Args) + 'static>(
        &mut self,
        step: &StepTypeWGHandler<F, Args, WG>,
        args_fn: impl Fn() -> Args,
    ) {
        while self.witness.step_instances.len() < self.num_steps {
            self.add(step, (args_fn)());
        }
    }
}

pub type Trace<F, TraceArgs> = dyn Fn(&mut TraceContext<F>, TraceArgs) + 'static;

pub struct TraceGenerator<F, TraceArgs> {
    trace: Rc<Trace<F, TraceArgs>>,
    num_steps: usize,
}

impl<F, TraceArgs> Clone for TraceGenerator<F, TraceArgs> {
    fn clone(&self) -> Self {
        Self {
            trace: self.trace.clone(),
            num_steps: self.num_steps,
        }
    }
}

impl<F, TraceArgs> Default for TraceGenerator<F, TraceArgs> {
    fn default() -> Self {
        Self {
            trace: Rc::new(|_, _| {}),
            num_steps: 0,
        }
    }
}

impl<F: Default, TraceArgs> TraceGenerator<F, TraceArgs> {
    pub fn new(trace: Rc<Trace<F, TraceArgs>>, num_steps: usize) -> Self {
        Self { trace, num_steps }
    }

    pub fn generate(&self, args: TraceArgs) -> TraceWitness<F> {
        let mut ctx = TraceContext::new(self.num_steps);

        (self.trace)(&mut ctx, args);

        ctx.get_witness()
    }
}

pub type FixedAssignment<F> = HashMap<Queriable<F>, Vec<F>>;

/// A struct that can be used a fixed column generation context. It provides an interface for
/// assigning values to fixed columns in a circuit at the specified offset.
pub struct FixedGenContext<F> {
    assignments: FixedAssignment<F>,
    num_steps: usize,
}

impl<F: Field + Hash> FixedGenContext<F> {
    pub fn new(num_steps: usize) -> Self {
        Self {
            assignments: Default::default(),
            num_steps,
        }
    }

    /// Takes a `Queriable` object representing the fixed column (lhs) and the value (rhs) to be
    /// assigned.
    pub fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F) {
        if !Self::is_fixed_queriable(lhs) {
            panic!("trying to assign non-fixed signal");
        }

        if let Some(assignments) = self.assignments.get_mut(&lhs) {
            assignments[offset] = rhs;
        } else {
            let mut assignments = vec![F::ZERO; self.num_steps];
            assignments[offset] = rhs;
            self.assignments.insert(lhs, assignments);
        }
    }

    pub fn get_assignments(self) -> FixedAssignment<F> {
        self.assignments
    }

    fn is_fixed_queriable(q: Queriable<F>) -> bool {
        matches!(q, Queriable::Halo2FixedQuery(_, _) | Queriable::Fixed(_, _))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{frontend::dsl::StepTypeWGHandler, util::uuid};

    fn dummy_args_fn() {}

    #[test]
    fn test_padding_no_witness() {
        let mut ctx = TraceContext::new(5);
        let step = StepTypeWGHandler::new(uuid(), "dummy", |_: &mut StepInstance<i32>, _: ()| {});

        assert_eq!(ctx.witness.step_instances.len(), 0);
        ctx.padding(&step, dummy_args_fn);

        assert_eq!(ctx.witness.step_instances.len(), 5);
    }

    #[test]
    fn test_padding_partial_witness() {
        let mut ctx = TraceContext::new(5);
        let step = StepTypeWGHandler::new(uuid(), "dummy", |_: &mut StepInstance<i32>, _: ()| {});

        dummy_args_fn();
        ctx.add(&step, ());

        assert_eq!(ctx.witness.step_instances.len(), 1);
        ctx.padding(&step, dummy_args_fn);

        assert_eq!(ctx.witness.step_instances.len(), 5);
    }
}
