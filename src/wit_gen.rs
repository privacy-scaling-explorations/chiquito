use std::{collections::HashMap, hash::Hash, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::{query::Queriable, StepTypeUUID},
    dsl::StepTypeWGHandler,
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

#[derive(Debug, Default)]
pub struct TraceContext<F> {
    witness: TraceWitness<F>,
    num_steps: usize,
}

impl<F> TraceContext<F> {
    pub fn new(num_steps: usize) -> Self {
        Self {
            witness: TraceWitness {
                step_instances: Vec::new(),
            },
            num_steps,
        }
    }

    pub fn get_witness(self) -> TraceWitness<F> {
        self.witness
    }
}

impl<F: Clone> TraceContext<F> {
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
    use std::{cell::RefCell, rc::Rc};

    use crate::dsl::{cb::eq, circuit};
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_padding_with_no_witness() {
        let number_steps = Rc::new(RefCell::new(0));
        let nowit = circuit("nowit", |ctx| {
            // This circuit has no signals; only those added in padding()
            let a_val = Fr::from(1); // Create a field element from integer
            let b_val = Fr::from(2); // Create a field element from integer
                                     // padding() should fill in all 10 steps
            ctx.pragma_num_steps(10);

            let nowit_step = ctx.step_type("nowit");

            // define padding step type; a + b = c
            let nowit_step = ctx.step_type_def(nowit_step, |ctx| {
                let a = ctx.internal("a");
                let b = ctx.internal("b");
                let c = ctx.internal("c");

                ctx.setup(move |ctx| {
                    ctx.constr(eq(a + b, c));
                });

                ctx.wg(move |ctx, (a_value, b_value): (Fr, Fr)| {
                    // Update the types here
                    ctx.assign(a, a_value);
                    ctx.assign(b, b_value);
                    ctx.assign(c, a_value + b_value);
                })
            });

            let number_steps_ref = Rc::clone(&number_steps);

            // Padding should fill the entire circuit
            ctx.trace(move |ctx: _, _args: (Fr, Fr)| {
                // Update the types here
                ctx.padding(&nowit_step, || (a_val, b_val));
                let witness_len = ctx.witness.step_instances.len();
                println!("Witness Length: {}", witness_len);
                *number_steps_ref.borrow_mut() = witness_len;
                assert_eq!(*number_steps_ref.borrow(), 10);
            })            
        });

        print!("{:?}", nowit);
        assert_eq!(*number_steps.borrow(), 10);
    }
}
