use crate::{
    ast::{query::Queriable, Circuit, StepType, StepTypeUUID},
    util::uuid,
    wit_gen::{FixedGenContext, StepInstance, TraceContext},
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use core::fmt::Debug;
use std::marker::PhantomData;

use self::cb::{Constraint, LookupBuilder, Typing};

/// A generic structure designed to handle the context of a circuit for generic types `F`,
/// `TraceArgs` and `StepArgs`. The struct contains a `Circuit` instance and implements
/// methods to build the circuit, add various components, and manipulate the circuit. `F` is a
/// generic type representing the field of the circuit. `TraceArgs` is a generic type
/// representing the arguments passed to the trace function. `StepArgs` is a generic type
/// representing the arguments passed to the `step_type_def` function.
pub struct CircuitContext<F, TraceArgs> {
    sc: Circuit<F, TraceArgs>,
}

impl<F, TraceArgs> CircuitContext<F, TraceArgs> {
    /// Adds a forward signal to the circuit with a name string and zero rotation and returns a
    /// `Queriable` instance representing the added forward signal.
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, 0), false)
    }

    /// Adds a forward signal to the circuit with a name string and a specified phase and returns a
    /// `Queriable` instance representing the added forward signal.
    pub fn forward_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, phase), false)
    }

    /// Adds a shared signal to the circuit with a name string and zero rotation and returns a
    /// `Queriable` instance representing the added shared signal.
    pub fn shared(&mut self, name: &str) -> Queriable<F> {
        Queriable::Shared(self.sc.add_shared(name, 0), 0)
    }

    /// Adds a shared signal to the circuit with a name string and a specified phase and returns a
    /// `Queriable` instance representing the added shared signal.
    pub fn shared_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Shared(self.sc.add_shared(name, phase), 0)
    }

    pub fn fixed(&mut self, name: &str) -> Queriable<F> {
        Queriable::Fixed(self.sc.add_fixed(name), 0)
    }

    /// Exposes the first step instance value of a forward signal as public.
    pub fn expose(&mut self, forward: Queriable<F>) {
        match forward {
            Queriable::Forward(forward_signal, _) => {
                self.sc.expose(forward_signal);
            }
            _ => panic!("Expected forward signal"),
        }
    }

    /// Imports a halo2 advice column with a name string into the circuit and returns a
    /// `Queriable` instance representing the imported column.
    pub fn import_halo2_advice(&mut self, name: &str, column: Halo2Column<Advice>) -> Queriable<F> {
        Queriable::Halo2AdviceQuery(self.sc.add_halo2_advice(name, column), 0)
    }

    /// Imports a halo2 fixed column with a name string into the circuit and returns a
    /// `Queriable` instance representing the imported column.
    pub fn import_halo2_fixed(&mut self, name: &str, column: Halo2Column<Fixed>) -> Queriable<F> {
        Queriable::Halo2FixedQuery(self.sc.add_halo2_fixed(name, column), 0)
    }

    /// Adds a new step type with the specified name to the circuit and returns a
    /// `StepTypeHandler` instance. The `StepTypeHandler` instance can be used to define the
    /// step type using the `step_type_def` function.
    pub fn step_type(&mut self, name: &str) -> StepTypeHandler {
        let handler = StepTypeHandler::new(name.to_string());

        self.sc.add_step_type(handler, name);

        handler
    }

    /// Defines a step type using the provided `StepTypeHandler` and a function that takes a
    /// mutable reference to a `StepTypeContext`. This function typically adds constraints to a
    /// step type and defines witness generation.
    pub fn step_type_def<D, Args, S: Into<StepTypeDefInput>, R>(
        &mut self,
        step: S,
        def: D,
    ) -> StepTypeWGHandler<F, Args, R>
    where
        D: FnOnce(&mut StepTypeContext<F>) -> StepTypeWGHandler<F, Args, R>,
        R: Fn(&mut StepInstance<F>, Args) + 'static,
    {
        let handler: StepTypeHandler = match step.into() {
            StepTypeDefInput::Handler(h) => h,
            StepTypeDefInput::String(name) => {
                let handler = StepTypeHandler::new(name.to_string());

                self.sc.add_step_type(handler, name);

                handler
            }
        };

        let mut context = StepTypeContext::<F>::new(handler.uuid(), handler.annotation.to_string());

        let result = def(&mut context);

        self.sc.add_step_type_def(context.step_type);

        result
    }

    /// Sets the trace function that builds the witness. The trace function is responsible for
    /// adding step instances defined in `step_type_def`. The function is entirely left for
    /// the user to implement and is Turing complete. Users typically use external parameters
    /// of type `TraceArgs` to generate cell values for witness generation, and call the
    /// `add` function to add step instances with witness values.
    pub fn trace<D>(&mut self, def: D)
    where
        D: Fn(&mut TraceContext<F>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
    }

    /// Sets the fixed generation function for the circuit. The fixed generation function is
    /// responsible for assigning fixed values to fixed columns. It is entirely left
    /// for the user to implement and is Turing complete. Users typically generate cell values and
    /// call the `assign` function to fill the fixed columns.
    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut FixedGenContext<F>) + 'static,
    {
        self.sc.set_fixed_gen(def);
    }

    /// Enforce the type of the first step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_first_step<STH: Into<StepTypeHandler>>(&mut self, step_type: STH) {
        self.sc.first_step = Some(step_type.into().uuid());
    }

    /// Enforce the type of the last step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_last_step<STH: Into<StepTypeHandler>>(&mut self, step_type: STH) {
        self.sc.last_step = Some(step_type.into().uuid());
    }

    pub fn pragma_num_steps(&mut self, num_steps: usize) {
        self.sc.num_steps = num_steps;
    }
}

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

/// A generic structure designed to handle the context of a step type definition.  The struct
/// contains a `StepType` instance and implements methods to build the step type, add components,
/// and manipulate the step type. `F` is a generic type representing the field of the step type.
/// `Args` is the type of the step instance witness generation arguments.
pub struct StepTypeContext<F> {
    step_type: StepType<F>,
}

impl<F> StepTypeContext<F> {
    pub fn new(uuid: u32, name: String) -> Self {
        Self {
            step_type: StepType::new(uuid, name),
        }
    }

    /// Adds an internal signal to the step type with the given name and returns a `Queriable`
    /// instance representing the added signal.
    pub fn internal(&mut self, name: &str) -> Queriable<F> {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    /// DEPRECATED
    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        println!("DEPRECATED constr: use setup for constraints in step types");

        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    /// DEPRECATED
    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        println!("DEPRECATED transition: use setup for constraints in step types");

        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    /// Define step constraints.
    pub fn setup<D>(&mut self, def: D)
    where
        D: Fn(&mut StepTypeSetupContext<F>),
    {
        let mut ctx = StepTypeSetupContext {
            step_type: &mut self.step_type,
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

            _p: PhantomData::default(),
        }
    }
}

impl<F: Debug + Clone> StepTypeContext<F> {
    /// DEPRECATED
    pub fn add_lookup(&mut self, lookup_builder: &mut LookupBuilder<F>) {
        println!("DEPRECATED add_lookup: use setup for constraints in step types");

        self.step_type.lookups.push(lookup_builder.lookup.clone());
    }
}

pub struct StepTypeSetupContext<'a, F> {
    step_type: &'a mut StepType<F>,
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

impl<'a, F: Debug + Clone> StepTypeSetupContext<'a, F> {
    /// Adds a lookup to the step type.
    pub fn add_lookup(&mut self, lookup_builder: &mut LookupBuilder<F>) {
        self.step_type.lookups.push(lookup_builder.lookup.clone());
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StepTypeHandler {
    id: StepTypeUUID,
    pub annotation: &'static str,
}

impl StepTypeHandler {
    fn new(annotation: String) -> Self {
        Self {
            id: uuid(),
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }

    pub fn next<F>(&self) -> Queriable<F> {
        Queriable::StepTypeNext(*self)
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
    id: u32,
    pub annotation: &'static str,
    pub wg: Box<D>,

    _p: PhantomData<(F, Args)>,
}

impl<F, Args, D: Fn(&mut StepInstance<F>, Args) + 'static> StepTypeWGHandler<F, Args, D> {
    pub fn uuid(&self) -> u32 {
        self.id
    }
}

/// Creates a `Circuit` instance by providing a name and a definition closure that is applied to a
/// mutable `CircuitContext`. The user customizes the definition closure by calling `CircuitContext`
/// functions. This is the main function that users call to define a Chiquito circuit. Currently,
/// the name is not used for annotation within the function, but it may be used in future
/// implementations.
pub fn circuit<F, TraceArgs, StepArgs, D>(_name: &str, def: D) -> Circuit<F, TraceArgs>
where
    D: Fn(&mut CircuitContext<F, TraceArgs>),
{
    // TODO annotate circuit
    let mut context = CircuitContext {
        sc: Circuit::default(),
    };

    def(&mut context);

    context.sc
}

pub mod cb;
