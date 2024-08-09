use crate::{
    field::Field,
    sbpir::{query::Queriable, ExposeOffset, SBPIRLegacy},
    wit_gen::{FixedGenContext, StepInstance, TraceGenerator},
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use core::{fmt::Debug, hash::Hash};

use super::{
    lb::{LookupTable, LookupTableRegistry, LookupTableStore},
    trace::{DSLTraceGenerator, TraceContext},
    StepTypeContext, StepTypeDefInput, StepTypeHandler, StepTypeWGHandler,
};

#[derive(Debug, Default)]
/// A generic structure designed to handle the context of a circuit.
/// The struct contains a `Circuit` instance and implements methods to build the circuit,
/// add various components, and manipulate the circuit.
///
/// ### Type parameters
/// `F` is the field of the circuit.
/// `TG` is the trace generator.
///
/// (LEGACY)
pub struct CircuitContextLegacy<F, TG: TraceGenerator<F> = DSLTraceGenerator<F>> {
    pub(crate) circuit: SBPIRLegacy<F, TG>,
    pub(crate) tables: LookupTableRegistry<F>,
}

impl<F, TG: TraceGenerator<F>> CircuitContextLegacy<F, TG> {
    /// Adds a forward signal to the circuit with a name string and zero rotation and returns a
    /// `Queriable` instance representing the added forward signal.
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.circuit.add_forward(name, 0), false)
    }

    /// Adds a forward signal to the circuit with a name string and a specified phase and returns a
    /// `Queriable` instance representing the added forward signal.
    pub fn forward_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Forward(self.circuit.add_forward(name, phase), false)
    }

    /// Adds a shared signal to the circuit with a name string and zero rotation and returns a
    /// `Queriable` instance representing the added shared signal.
    pub fn shared(&mut self, name: &str) -> Queriable<F> {
        Queriable::Shared(self.circuit.add_shared(name, 0), 0)
    }

    /// Adds a shared signal to the circuit with a name string and a specified phase and returns a
    /// `Queriable` instance representing the added shared signal.
    pub fn shared_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Shared(self.circuit.add_shared(name, phase), 0)
    }

    pub fn fixed(&mut self, name: &str) -> Queriable<F> {
        Queriable::Fixed(self.circuit.add_fixed(name), 0)
    }

    /// Exposes the first step instance value of a forward signal as public.
    pub fn expose(&mut self, queriable: Queriable<F>, offset: ExposeOffset) {
        self.circuit.expose(queriable, offset);
    }

    /// Imports a halo2 advice column with a name string into the circuit and returns a
    /// `Queriable` instance representing the imported column.
    pub fn import_halo2_advice(&mut self, name: &str, column: Halo2Column<Advice>) -> Queriable<F> {
        Queriable::Halo2AdviceQuery(self.circuit.add_halo2_advice(name, column), 0)
    }

    /// Imports a halo2 fixed column with a name string into the circuit and returns a
    /// `Queriable` instance representing the imported column.
    pub fn import_halo2_fixed(&mut self, name: &str, column: Halo2Column<Fixed>) -> Queriable<F> {
        Queriable::Halo2FixedQuery(self.circuit.add_halo2_fixed(name, column), 0)
    }

    /// Adds a new step type with the specified name to the circuit and returns a
    /// `StepTypeHandler` instance. The `StepTypeHandler` instance can be used to define the
    /// step type using the `step_type_def` function.
    pub fn step_type(&mut self, name: &str) -> StepTypeHandler {
        let handler = StepTypeHandler::new(name.to_string());

        self.circuit.add_step_type(handler, name);

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

                self.circuit.add_step_type(handler, name);

                handler
            }
        };

        let mut context = StepTypeContext::<F>::new(
            handler.uuid(),
            handler.annotation.to_string(),
            self.tables.clone(),
        );

        let result = def(&mut context);

        self.circuit.add_step_type_def(context.step_type);

        result
    }

    pub fn new_table(&self, table: LookupTableStore<F>) -> LookupTable {
        let uuid = table.uuid();
        self.tables.add(table);

        LookupTable { uuid }
    }

    /// Enforce the type of the first step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_first_step<STH: Into<StepTypeHandler>>(&mut self, step_type: STH) {
        self.circuit.first_step = Some(step_type.into().uuid());
    }

    /// Enforce the type of the last step by adding a constraint to the circuit. Takes a
    /// `StepTypeHandler` parameter that represents the step type.
    pub fn pragma_last_step<STH: Into<StepTypeHandler>>(&mut self, step_type: STH) {
        self.circuit.last_step = Some(step_type.into().uuid());
    }

    /// Enforce the number of step instances by adding a constraint to the circuit. Takes a `usize`
    /// parameter that represents the total number of steps.
    pub fn pragma_num_steps(&mut self, num_steps: usize) {
        self.circuit.num_steps = num_steps;
    }

    pub fn pragma_disable_q_enable(&mut self) {
        self.circuit.q_enable = false;
    }
}

impl<F: Field, TraceArgs: Clone> CircuitContextLegacy<F, DSLTraceGenerator<F, TraceArgs>> {
    /// Sets the trace function that builds the witness. The trace function is responsible for
    /// adding step instances defined in `step_type_def`. The function is entirely left for
    /// the user to implement and is Turing complete. Users typically use external parameters
    /// of type `TraceArgs` to generate cell values for witness generation, and call the
    /// `add` function to add step instances with witness values.
    pub fn trace<D>(&mut self, def: D)
    where
        D: Fn(&mut TraceContext<F>, TraceArgs) + 'static,
    {
        self.circuit.set_trace(def);
    }
}

impl<F: Field + Hash, TG: TraceGenerator<F>> CircuitContextLegacy<F, TG> {
    /// Executes the fixed generation function provided by the user and sets the fixed assignments
    /// for the circuit. The fixed generation function is responsible for assigning fixed values to
    /// fixed columns. It is entirely left for the user to implement and is Turing complete. Users
    /// typically generate cell values and call the `assign` function to fill the fixed columns.
    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut FixedGenContext<F>) + 'static,
    {
        if self.circuit.num_steps == 0 {
            panic!("circuit must call pragma_num_steps before calling fixed_gen");
        }
        let mut ctx = FixedGenContext::new(self.circuit.num_steps);
        (def)(&mut ctx);

        let assignments = ctx.get_assignments();

        self.circuit.set_fixed_assignments(assignments);
    }
}

/// Creates a `Circuit` instance by providing a name and a definition closure that is applied to a
/// mutable `CircuitContext`. The user customizes the definition closure by calling `CircuitContext`
/// functions. This is the main function that users call to define a Chiquito circuit (legacy).
pub fn circuit_legacy<F: Field, TraceArgs: Clone, D>(
    _name: &str,
    mut def: D,
) -> SBPIRLegacy<F, DSLTraceGenerator<F, TraceArgs>>
where
    D: FnMut(&mut CircuitContextLegacy<F, DSLTraceGenerator<F, TraceArgs>>),
{
    // TODO annotate circuit
    let mut context = CircuitContextLegacy {
        circuit: SBPIRLegacy::default(),
        tables: LookupTableRegistry::default(),
    };

    def(&mut context);

    context.circuit
}
