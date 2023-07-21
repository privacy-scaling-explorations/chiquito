use std::{collections::HashMap, hash::Hash, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::{query::Queriable, StepTypeUUID, StepType},
    dsl::{StepTypeWGHandler, StepTypeHandler},
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

// returning a Vec<F> makes it so that TraceArgs don't have to be passed to TraceContext's generics
pub type PaddingLambda<F> = dyn Fn() -> Vec<F> + 'static;

#[derive(Debug, Default)]
pub struct TraceContext<F> {
    witness: TraceWitness<F>,
    padding: Option<(StepTypeUUID, PaddingLambda<F>)>
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

    // This is an external function users can use to create their own padding constraint vs. the default
    pub fn set_padding<Args, WG: Fn(&mut StepInstance<F>, Args) + 'static>(&mut self, step_handler: &StepTypeHandler, lambda: PaddingLambda<F>) {
        self.padding = Some((step_handler.uuid(), lambda));
    }

    // this function pads the rest of the circuit with the 
    // StepInstance of the StepType in TraceContext::padding
    fn pad(&mut self) {
        // here we set the padding
        while self.witness.step_instances.len() < self.witness.height {
            if let Some((padding_uuid, padding_lambda)) = &self.padding {
                let mut padded_witness = StepInstance::new(*padding_uuid);

                // How should these TraceArgs be used? How do we add them to this scope without changing the type parameters for TraceContext?
                let trace_args = padding_lambda();

                self.witness.step_instances.push(padded_witness);
            } else {
                panic!("Missing padding step!");
            }
        }
    }
}

pub type Trace<F, TraceArgs> = dyn Fn(&mut TraceContext<F>, TraceArgs) + 'static;

pub struct TraceGenerator<F, TraceArgs> {
    trace: Rc<Trace<F, TraceArgs>>,
}

impl<F, TraceArgs> Clone for TraceGenerator<F, TraceArgs> {
    fn clone(&self) -> Self {
        Self {
            trace: self.trace.clone(),
        }
    }
}

impl<F: Default, TraceArgs> TraceGenerator<F, TraceArgs> {
    pub fn new(trace: Rc<Trace<F, TraceArgs>>) -> Self {
        Self { trace }
    }

    pub fn generate(&self, args: TraceArgs) -> TraceWitness<F> {
        let mut ctx = TraceContext::default();

        (self.trace)(&mut ctx, args);

        // pad the circuit before getting the witness
        ctx.pad();

        ctx.get_witness()
    }
}

pub type FixedAssignment<F> = HashMap<Queriable<F>, Vec<F>>;

/// A struct that can be used a fixed column generation context. It provides an interface for
/// assigning values to fixed columns in a circuit at the specified offset.
pub struct FixedGenContext<F> {
    assigments: FixedAssignment<F>,
    num_steps: usize,
}

impl<F: Field + Hash> FixedGenContext<F> {
    pub fn new(num_steps: usize) -> Self {
        Self {
            assigments: Default::default(),
            num_steps,
        }
    }

    /// Takes a `Queriable` object representing the fixed column (lhs) and the value (rhs) to be
    /// assigned.
    pub fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F) {
        if !Self::is_fixed_queriable(lhs) {
            panic!("trying to assign non-fixed signal");
        }

        if let Some(assigments) = self.assigments.get_mut(&lhs) {
            assigments[offset] = rhs;
        } else {
            let mut assigments = vec![F::ZERO; self.num_steps];
            assigments[offset] = rhs;
            self.assigments.insert(lhs, assigments);
        }
    }

    pub fn get_assigments(self) -> FixedAssignment<F> {
        self.assigments
    }

    fn is_fixed_queriable(q: Queriable<F>) -> bool {
        matches!(q, Queriable::Halo2FixedQuery(_, _) | Queriable::Fixed(_, _))
    }
}
