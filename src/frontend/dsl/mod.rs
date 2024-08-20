use crate::{
    sbpir::{query::Queriable, StepType, StepTypeUUID, PIR},
    util::{uuid, UUID},
    wit_gen::StepInstance,
};

use core::{fmt::Debug, hash::Hash};
use std::marker::PhantomData;

use self::{
    cb::{eq, Constraint, Typing},
    lb::{LookupBuilder, LookupTableRegistry},
};

pub use sc::*;

pub mod cb;
pub mod circuit_context_legacy;
pub mod lb;
pub mod sc;
pub mod trace;

pub enum StepTypeDefInput {
    Handler(StepTypeHandler),
    String(&'static str),
}

impl From<StepTypeHandler> for StepTypeDefInput {
    fn from(h: StepTypeHandler) -> Self {
        StepTypeDefInput::Handler(h)
    }
}

impl From<&'static str> for StepTypeDefInput {
    fn from(s: &'static str) -> Self {
        StepTypeDefInput::String(s)
    }
}

impl From<String> for StepTypeDefInput {
    fn from(s: String) -> Self {
        StepTypeDefInput::String(Box::leak(s.into_boxed_str()))
    }
}

/// A generic structure designed to handle the context of a step type definition.  The struct
/// contains a `StepType` instance and implements methods to build the step type, add components,
/// and manipulate the step type. `F` is a generic type representing the field of the step type.
/// `Args` is the type of the step instance witness generation arguments.
pub struct StepTypeContext<F> {
    step_type: StepType<F>,
    tables: LookupTableRegistry<F>,
}

impl<F> StepTypeContext<F> {
    pub fn new(uuid: UUID, name: String, tables: LookupTableRegistry<F>) -> Self {
        Self {
            step_type: StepType::new(uuid, name),
            tables,
        }
    }

    /// Adds an internal signal to the step type with the given name and returns a `Queriable`
    /// instance representing the added signal.
    pub fn internal(&mut self, name: &str) -> Queriable<F> {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    /// DEPRECATED
    // #[deprecated(note = "use step types setup for constraints instead")]
    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        println!("DEPRECATED constr: use setup for constraints in step types");

        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    /// DEPRECATED
    #[deprecated(note = "use step types setup for constraints instead")]
    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        println!("DEPRECATED transition: use setup for constraints in step types");

        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    /// Define step constraints.
    pub fn setup<D>(&mut self, mut def: D)
    where
        D: FnMut(&mut StepTypeSetupContext<F>),
    {
        let mut ctx = StepTypeSetupContext {
            step_type: &mut self.step_type,
            tables: self.tables.clone(),
        };

        def(&mut ctx);
    }

    pub fn wg<Args, D>(&mut self, def: D) -> StepTypeWGHandler<F, Args, D>
    where
        D: Fn(&mut StepInstance<F>, Args) + 'static,
    {
        StepTypeWGHandler {
            id: self.step_type.uuid(),
            annotation: Box::leak(self.step_type.name.clone().into_boxed_str()),

            wg: Box::new(def),

            _p: PhantomData,
        }
    }
}

pub struct StepTypeSetupContext<'a, F> {
    step_type: &'a mut StepType<F>,
    tables: LookupTableRegistry<F>,
}

impl<'a, F> StepTypeSetupContext<'a, F> {
    /// Adds a constraint to the step type. Involves internal signal(s) and forward signals without
    /// SuperRotation only. Chiquito provides syntax sugar for defining complex constraints.
    /// Refer to the `cb` (constraint builder) module for more information.
    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();
        Self::enforce_constraint_typing(&constraint);

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    /// Adds a transition constraint to the step type. It’s the same as a regular constraint except
    /// that it can involve forward signal(s) with SuperRotation as well. Chiquito provides syntax
    /// sugar for defining complex constraints. Refer to the `cb` (constraint builder) module
    /// for more information.
    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();
        Self::enforce_constraint_typing(&constraint);

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    fn enforce_constraint_typing(constraint: &Constraint<F>) {
        if constraint.typing != Typing::AntiBooly {
            panic!(
                "Expected AntiBooly constraint, got {:?} (constraint: {})",
                constraint.typing, constraint.annotation
            );
        }
    }
}

impl<'a, F: Eq + PartialEq + Hash + Debug + Clone> StepTypeSetupContext<'a, F> {
    pub fn auto(&mut self, signal: Queriable<F>, expr: PIR<F>) {
        self.step_type.auto_signals.insert(signal, expr);
    }

    pub fn auto_eq(&mut self, signal: Queriable<F>, expr: PIR<F>) {
        self.auto(signal.clone(), expr.clone());

        self.constr(eq(signal, expr));
    }
}

impl<'a, F: Debug + Clone> StepTypeSetupContext<'a, F> {
    /// Adds a lookup to the step type.
    pub fn add_lookup<LB: LookupBuilder<F>>(&mut self, lookup_builder: LB) {
        self.step_type.lookups.push(lookup_builder.build(self));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StepTypeHandler {
    id: StepTypeUUID,
    pub annotation: &'static str,
}

impl StepTypeHandler {
    pub(crate) fn new(annotation: String) -> Self {
        Self {
            id: uuid(),
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn new_with_id(id: UUID, annotation: String) -> Self {
        Self {
            id,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }

    pub fn next<F>(&self) -> Queriable<F> {
        Queriable::StepTypeNext(*self)
    }

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }
}

impl<F, Args, D: Fn(&mut StepInstance<F>, Args) + 'static> From<&StepTypeWGHandler<F, Args, D>>
    for StepTypeHandler
{
    fn from(h: &StepTypeWGHandler<F, Args, D>) -> Self {
        StepTypeHandler {
            id: h.id,
            annotation: h.annotation,
        }
    }
}

pub struct StepTypeWGHandler<F, Args, D: Fn(&mut StepInstance<F>, Args) + 'static> {
    id: UUID,
    pub annotation: &'static str,
    pub wg: Box<D>,

    _p: PhantomData<(F, Args)>,
}

impl<F, Args, D: Fn(&mut StepInstance<F>, Args) + 'static> StepTypeWGHandler<F, Args, D> {
    pub fn new(id: UUID, annotation: &'static str, wg: D) -> Self {
        StepTypeWGHandler {
            id,
            annotation,
            wg: Box::new(wg),
            _p: PhantomData,
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }
}

#[cfg(test)]
mod tests {
    use circuit_context_legacy::CircuitContextLegacy;
    use halo2_proofs::halo2curves::bn256::Fr;
    use trace::DSLTraceGenerator;

    use crate::{
        sbpir::{ExposeOffset, ForwardSignal, SBPIRLegacy},
        wit_gen::{NullTraceGenerator, TraceGenerator},
    };

    use super::*;

    fn setup_circuit_context<F, TG>() -> CircuitContextLegacy<F, TG>
    where
        F: Default,
        TG: TraceGenerator<F>,
    {
        CircuitContextLegacy {
            circuit: SBPIRLegacy::default(),
            tables: Default::default(),
        }
    }

    #[test]
    fn test_circuit_default_initialization() {
        let circuit: SBPIRLegacy<i32, NullTraceGenerator> = SBPIRLegacy::default();

        // Assert default values
        assert!(circuit.step_types.is_empty());
        assert!(circuit.forward_signals.is_empty());
        assert!(circuit.shared_signals.is_empty());
        assert!(circuit.fixed_signals.is_empty());
        assert!(circuit.exposed.is_empty());
        assert!(circuit.annotations.is_empty());
        assert!(circuit.trace_generator.is_none());
        assert!(circuit.first_step.is_none());
        assert!(circuit.last_step.is_none());
        assert!(circuit.num_steps == 0);
        assert!(circuit.q_enable);
    }

    #[test]
    fn test_disable_q_enable() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();
        context.pragma_disable_q_enable();
        assert!(!context.circuit.q_enable);
    }

    #[test]
    fn test_set_num_steps() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        context.pragma_num_steps(3);
        assert_eq!(context.circuit.num_steps, 3);

        context.pragma_num_steps(0);
        assert_eq!(context.circuit.num_steps, 0);
    }

    #[test]
    fn test_set_first_step() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        let step_type: StepTypeHandler = context.step_type("step_type");

        context.pragma_first_step(step_type);
        assert_eq!(context.circuit.first_step, Some(step_type.uuid()));
    }

    #[test]
    fn test_set_last_step() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        let step_type: StepTypeHandler = context.step_type("step_type");

        context.pragma_last_step(step_type);
        assert_eq!(context.circuit.last_step, Some(step_type.uuid()));
    }

    #[test]
    fn test_forward() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set forward signals
        let forward_a: Queriable<i32> = context.forward("forward_a");
        let forward_b: Queriable<i32> = context.forward("forward_b");

        // assert forward signals are correct
        assert_eq!(context.circuit.forward_signals.len(), 2);
        assert_eq!(context.circuit.forward_signals[0].uuid(), forward_a.uuid());
        assert_eq!(context.circuit.forward_signals[1].uuid(), forward_b.uuid());
    }

    #[test]
    fn test_adding_duplicate_signal_names() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();
        context.forward("duplicate_name");
        context.forward("duplicate_name");
        // Assert how the system should behave. Does it override the previous signal, throw an
        // error, or something else?
        // TODO: Should we let the user know that they are adding a duplicate signal name? And let
        // the circuit have two signals with the same name?
        assert_eq!(context.circuit.forward_signals.len(), 2);
    }

    #[test]
    fn test_forward_with_phase() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set forward signals with specified phase
        context.forward_with_phase("forward_a", 1);
        context.forward_with_phase("forward_b", 2);

        // assert forward signals are correct
        assert_eq!(context.circuit.forward_signals.len(), 2);
        assert_eq!(context.circuit.forward_signals[0].phase(), 1);
        assert_eq!(context.circuit.forward_signals[1].phase(), 2);
    }

    #[test]
    fn test_shared() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set shared signal
        let shared_a: Queriable<i32> = context.shared("shared_a");

        // assert shared signal is correct
        assert_eq!(context.circuit.shared_signals.len(), 1);
        assert_eq!(context.circuit.shared_signals[0].uuid(), shared_a.uuid());
    }

    #[test]
    fn test_shared_with_phase() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set shared signal with specified phase
        context.shared_with_phase("shared_a", 2);

        // assert shared signal is correct
        assert_eq!(context.circuit.shared_signals.len(), 1);
        assert_eq!(context.circuit.shared_signals[0].phase(), 2);
    }

    #[test]
    fn test_fixed() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set fixed signal
        context.fixed("fixed_a");

        // assert fixed signal was added to the circuit
        assert_eq!(context.circuit.fixed_signals.len(), 1);
    }

    #[test]
    fn test_expose() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // set forward signal and step to expose
        let forward_a: Queriable<i32> = context.forward("forward_a");
        let step_offset: ExposeOffset = ExposeOffset::Last;

        // expose the forward signal of the final step
        context.expose(forward_a, step_offset);

        // assert the signal is exposed
        assert_eq!(context.circuit.exposed[0].0, forward_a);
        assert_eq!(
            std::mem::discriminant(&context.circuit.exposed[0].1),
            std::mem::discriminant(&step_offset)
        );
    }

    #[test]
    #[ignore]
    #[should_panic(expected = "Signal not found")]
    fn test_expose_non_existing_signal() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();
        let non_existing_signal =
            Queriable::Forward(ForwardSignal::new_with_phase(0, "".to_owned()), false); // Create a signal not added to the circuit
        context.expose(non_existing_signal, ExposeOffset::First);

        todo!("remove the ignore after fixing the check for non existing signals")
    }

    #[test]
    fn test_step_type() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // create a step type
        let handler: StepTypeHandler = context.step_type("fibo_first_step");

        // assert that the created step type was added to the circuit annotations
        assert_eq!(
            context.circuit.annotations[&handler.uuid()],
            "fibo_first_step"
        );
    }

    #[test]
    fn test_step_type_def() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // create a step type including its definition
        let simple_step = context.step_type_def("simple_step", |context| {
            context.setup(|_| {});
            context.wg(|_, _: u32| {})
        });

        // assert step type was created and added to the circuit
        assert_eq!(
            context.circuit.annotations[&simple_step.uuid()],
            "simple_step"
        );
        assert_eq!(
            simple_step.uuid(),
            context.circuit.step_types[&simple_step.uuid()].uuid()
        );
    }

    #[test]
    fn test_step_type_def_pass_handler() {
        let mut context = setup_circuit_context::<i32, NullTraceGenerator>();

        // create a step type handler
        let handler: StepTypeHandler = context.step_type("simple_step");

        // create a step type including its definition
        let simple_step = context.step_type_def(handler, |context| {
            context.setup(|_| {});
            context.wg(|_, _: u32| {})
        });

        // assert step type was created and added to the circuit
        assert_eq!(
            context.circuit.annotations[&simple_step.uuid()],
            "simple_step"
        );
        assert_eq!(
            simple_step.uuid(),
            context.circuit.step_types[&simple_step.uuid()].uuid()
        );
    }

    #[test]
    fn test_trace() {
        let mut context = setup_circuit_context::<Fr, DSLTraceGenerator<Fr, i32>>();

        // set trace function
        context.trace(|_, _: i32| {});

        // assert trace function was set
        assert!(context.circuit.trace_generator.is_some());
    }

    #[test]
    #[should_panic(expected = "circuit cannot have more than one trace generator")]
    fn test_setting_trace_multiple_times() {
        let mut context = setup_circuit_context::<Fr, DSLTraceGenerator<Fr, i32>>();
        context.trace(|_, _| {});
        context.trace(|_, _| {});
    }
}
