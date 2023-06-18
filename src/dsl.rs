use crate::{
    ast::{query::Queriable, Circuit, StepType, StepTypeUUID},
    compiler::{FixedGenContext, TraceContext, WitnessGenContext},
    util::uuid,
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use core::fmt::Debug;

use self::cb::{Constraint, LookupBuilder};

/// A generic structure designed to handle the context of a circuit for generic types `F`,
/// `TraceArgs` and `StepArgs`. The struct contains a `Circuit` instance and implements
/// methods to build the circuit, add various components, and manipulate the circuit. `F` is a
/// generic type representing the field of the circuit. `TraceArgs` is a generic type
/// representing the arguments passed to the trace function. `StepArgs` is a generic type
/// representing the arguments passed to the `step_type_def` function.
pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: Circuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
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
    pub fn step_type_def<D>(&mut self, handler: StepTypeHandler, def: D)
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context =
            StepTypeContext::<F, StepArgs>::new(handler.uuid(), handler.annotation.to_string());

        def(&mut context);

        self.sc.add_step_type_def(context.step_type);
    }

    /// Sets the trace function that builds the circuit. The trace function is responsible for
    /// adding step instances defined in `step_type_def`. The function is entirely left for
    /// the user to implement and is Turing complete. Users typically use external parameters
    /// defined in `TraceArgs` to generate cell values for witness generation, and call the
    /// `add` function to add step instances with witness values.
    pub fn trace<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
    }

    /// Sets the fixed generation function for the circuit. The fixed generation function is
    /// responsible for assigning fixed values to fixed column `Queriable`. It is entirely left
    /// for the user to implement and is Turing complete. Users typically generate cell values and
    /// call the `assign` function to fill the fixed columns.
    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn FixedGenContext<F>) + 'static,
    {
        self.sc.set_fixed_gen(def);
    }

    /// Enforce the type of the first step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_first_step(&mut self, step_type: StepTypeHandler) {
        self.sc.first_step = Some(step_type);
    }

    /// Enforce the type of the last step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_last_step(&mut self, step_type: StepTypeHandler) {
        self.sc.last_step = Some(step_type);
    }
}

/// A generic structure designed to handle the context of a step type for generic types `F` and
/// `Args`. The struct contains a `StepType` instance and implements methods to build the
/// step type, add components, and manipulate the step type. `F` is a generic type representing
/// the field of the step type. `Args` is a generic type representing the arguments passed to
/// the step type.
pub struct StepTypeContext<F, Args> {
    step_type: StepType<F, Args>,
}

impl<F, Args> StepTypeContext<F, Args> {
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
        D: Fn(&mut StepTypeSetupContext<F, Args>),
    {
        let mut ctx = StepTypeSetupContext {
            step_type: &mut self.step_type,
        };

        def(&mut ctx);
    }

    /// Sets the witness generation function for the step type. The witness generation function is
    /// responsible for assigning witness values to witness column `Queriable`. It is entirely
    /// left for the user to implement and is Turing complete. Users typically generate cell values
    /// and call the assign function to fill the witness columns. `Args` is a generic type
    /// representing the arguments passed to the witness generation function.
    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

impl<F: Debug + Clone, Args> StepTypeContext<F, Args> {
    /// DEPRECATED
    pub fn add_lookup(&mut self, lookup_builder: &mut LookupBuilder<F>) {
        println!("DEPRECATED add_lookup: use setup for constraints in step types");

        self.step_type.lookups.push(lookup_builder.lookup.clone());
    }
}

pub struct StepTypeSetupContext<'a, F, Args> {
    step_type: &'a mut StepType<F, Args>,
}

impl<'a, F, Args> StepTypeSetupContext<'a, F, Args> {
    /// Adds a constraint to the step type. Involves internal signal(s) and forward signals without
    /// SuperRotation only. Chiquito provides syntax sugar for defining complex constraints.
    /// Refer to the `cb` (constraint builder) module for more information.
    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    /// Adds a transition constraint to the step type. It’s the same as a regular constraint except
    /// that it can involve forward signal(s) with SuperRotation as well. Chiquito provides syntax
    /// sugar for defining complex constraints. Refer to the `cb` (constraint builder) module
    /// for more information.
    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }
}

impl<'a, F: Debug + Clone, Args> StepTypeSetupContext<'a, F, Args> {
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

pub struct ForwardSignalHandler {
    // fs: ForwardSignal,
}

/// Creates a `Circuit` instance by providing a name and a definition closure that is applied to a
/// mutable `CircuitContext`. The user customizes the definition closure by calling `CircuitContext`
/// functions. This is the main function that users call to define a Chiquito circuit. Currently,
/// the name is not used for annotation within the function, but it may be used in future
/// implementations.
pub fn circuit<F, TraceArgs, StepArgs, D>(_name: &str, def: D) -> Circuit<F, TraceArgs, StepArgs>
where
    D: Fn(&mut CircuitContext<F, TraceArgs, StepArgs>),
{
    // TODO annotate circuit
    let mut context = CircuitContext {
        sc: Circuit::default(),
    };

    def(&mut context);

    context.sc
}

pub mod cb;
