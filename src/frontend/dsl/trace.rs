use std::rc::Rc;

use crate::{
    field::Field,
    wit_gen::{StepInstance, TraceGenerator, TraceWitness},
};

use super::StepTypeWGHandler;

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

/// A trace generator used by the DSL. Generates a trace witness
/// by calling the trace function with the given arguments.
///
/// ### Parameters
/// - `F`: The field type.
/// - `TA`: The type of arguments that the trace function takes.
///
/// ### Fields
/// - `trace`: The trace function.
/// - `num_steps`: The number of steps in the circuit.
pub struct DSLTraceGenerator<F, TA = ()> {
    trace: Rc<Trace<F, TA>>,
    num_steps: usize,
}

impl<F, TA> Clone for DSLTraceGenerator<F, TA> {
    fn clone(&self) -> Self {
        Self {
            trace: self.trace.clone(),
            num_steps: self.num_steps,
        }
    }
}

impl<F, TA> Default for DSLTraceGenerator<F, TA> {
    fn default() -> Self {
        Self {
            trace: Rc::new(|_, _| {}),
            num_steps: 0,
        }
    }
}

impl<F, TA> DSLTraceGenerator<F, TA> {
    /// Creates an instance.
    pub fn new(trace: Rc<Trace<F, TA>>, num_steps: usize) -> Self {
        Self { trace, num_steps }
    }
}

impl<F: Field, TA> TraceGenerator<F> for DSLTraceGenerator<F, TA> {
    type TraceArgs = TA;

    fn generate(&self, args: TA) -> TraceWitness<F> {
        let mut ctx = TraceContext::new(self.num_steps);
        (self.trace)(&mut ctx, args);
        ctx.get_witness()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        frontend::dsl::{trace::TraceContext, StepTypeWGHandler},
        util::uuid,
        wit_gen::StepInstance,
    };

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
