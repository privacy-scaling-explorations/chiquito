use crate::{
    ast::{query::Queriable, Circuit, Expr, StepType, StepTypeUUID, Lookup},
    compiler::{FixedGenContext, TraceContext, WitnessGenContext},
    util::uuid,
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use core::fmt::Debug;

use self::cb::{Constraint, LookupBuilder};

/// The **`CircuitContext`** struct is a generic structure designed to handle the context of a circuit for generic types **`F`**, **`TraceArgs`** and **`StepArgs`**. The struct contains a **`Circuit`** instance and implements methods to build the circuit, add various components, and manipulate the circuit.
/// **Type Parameters**
/// - **`F`**: A generic type representing the field of the circuit.
/// - **`TraceArgs`**: A generic type representing the arguments passed to the trace function.
/// - **`StepArgs`**: A generic type representing the arguments passed to the step_type_def function.
pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: Circuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
    /// # **Description:**
    /// Adds a forward signal to the circuit with zero rotation and returns a **`Queriable`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the forward signal.
    /// # **Return:**
    /// - **`Queriable<F>`** - A **`Queriable`** instance representing the added forward signal.    
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, 0), false)
    }

    /// # **Description:**
    /// Adds a forward signal to the circuit with the specified phase and returns a **`Queriable`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the forward signal.
    /// - **`phase: usize`** - The phase of the forward signal.
    /// # **Return:**
    /// - **`Queriable<F>`** - A **`Queriable`** instance representing the added forward signal.
    pub fn forward_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, phase), false)
    }

    /// # **Description:**
    /// Imports a halo2 advice column into the circuit and returns a **`Queriable`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the halo2 advice column.
    /// - **`column: Halo2Column<Advice>`** - The advice column to import.
    /// # **Return:**
    /// - **`Queriable<F>`** - A **`Queriable`** instance representing the imported halo2 advice column.
    pub fn import_halo2_advice(&mut self, name: &str, column: Halo2Column<Advice>) -> Queriable<F> {
        Queriable::Halo2AdviceQuery(self.sc.add_halo2_advice(name, column), 0)
    }

    /// # **Description:**
    /// Imports a halo2 fixed column into the circuit and returns a **`Queriable`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the halo2 fixed column.
    /// - **`column: Halo2Column<Fixed>`** - The fixed column to import.
    /// # **Return:**
    /// - **`Queriable<F>`** - A **`Queriable`** instance representing the imported halo2 fixed column.
    pub fn import_halo2_fixed(&mut self, name: &str, column: Halo2Column<Fixed>) -> Queriable<F> {
        Queriable::Halo2FixedQuery(self.sc.add_halo2_fixed(name, column), 0)
    }

    /// # **Description:**
    /// Adds a new step type with the specified name to the circuit and returns a **`StepTypeHandler`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the new step type.
    /// # **Return:**
    /// - **`StepTypeHandler`** - A **`StepTypeHandler`** instance representing the added step type.
    pub fn step_type(&mut self, name: &str) -> StepTypeHandler {
        let handler = StepTypeHandler::new(name.to_string());

        self.sc.add_step_type(handler, name);

        handler
    }

    /// # **Description:**
    /// Defines a step type using the provided **`StepTypeHandler`** and a function that takes a mutable reference to a **`StepTypeContext`**. This function typically adds constraints to a step type and defines witness generation.
    /// # **Arguments:**
    /// - **`handler: StepTypeHandler`** - The **`StepTypeHandler`** instance representing the step type to define.
    /// - **`def: D`** - The function that defines the step type by taking a mutable reference to a **`StepTypeContext`**.
    pub fn step_type_def<D>(&mut self, handler: StepTypeHandler, def: D)
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context =
            StepTypeContext::<F, StepArgs>::new(handler.uuid(), handler.annotation.to_string());

        def(&mut context);

        self.sc.add_step_type_def(context.step_type);
    }

    /// # **Description:**
    /// Sets the trace function for the circuit. The trace function is responsible for adding step instantiations defined in step_type_def.
    /// # **Arguments:**
    /// - **`def: D`** - The trace function, which takes a mutable reference to a **`TraceContext`** and a **`TraceArgs`** instance.
    pub fn trace<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
    }

    /// # **Description:**
    /// Sets the fixed generation function for the circuit. The fixed generation function is responsible for assigning fixed values to fixed column **`Queriable`**. It is entirely left for the user to implement and is Turing complete. Users typically generate cell values and call the `**assign**` function to fill the fixed columns.
    /// # **Arguments:**
    /// - **`def: D`** - The fixed generation function, which takes a mutable reference to a **`FixedGenContext`**. See more information about this trait and its assign function below.
    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn FixedGenContext<F>) + 'static,
    {
        self.sc.set_fixed_gen(def);
    }

    /// # **Description:**
    /// Enforce the type of the first step by adding a constraint to the circuit.
    /// # **Arguments:**
    /// - **`step_type: StepTypeHandler`** - The **`StepTypeHandler`** instance representing the first step type to enforce.
    pub fn pragma_first_step(&mut self, step_type: StepTypeHandler) {
        self.sc.first_step = Some(step_type);
    }

    /// # **Description:**
    /// Enforce the type of the last step by adding a constraint to the circuit.
    /// # **Arguments:**
    /// - **`step_type: StepTypeHandler`** - The **`StepTypeHandler`** instance representing the last step type to enforce.
    pub fn pragma_last_step(&mut self, step_type: StepTypeHandler) {
        self.sc.last_step = Some(step_type);
    }
}

/// The **`StepTypeContext`** struct is a generic structure designed to handle the context of a step type for generic types **`F`** and **`Args`**. The struct contains a **`StepType`** instance and implements methods to build the step type, add components, and manipulate the step type.
/// **Type Parameters**
/// - **`F`**: A generic type representing the field of the step type.
/// - **`Args`**: A generic type representing the arguments passed to the step type.
pub struct StepTypeContext<F, Args> {
    step_type: StepType<F, Args>,
}

impl<F, Args> StepTypeContext<F, Args> {
    pub fn new(uuid: u32, name: String) -> Self {
        Self {
            step_type: StepType::new(uuid, name),
        }
    }

    /// # **Description:**
    /// Adds an internal signal to the step type with the given name and returns a **`Queriable`** instance.
    /// # **Arguments:**
    /// - **`name: &str`** - The name of the internal signal.
    /// # **Return:**
    /// - **`Queriable<F>`** - A **`Queriable`** instance representing the added internal signal.
    pub fn internal(&mut self, name: &str) -> Queriable<F> {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    /// # **Description:**
    /// Adds a constraint to the step type. Involves internal signal(s) only.
    /// # **Arguments:**
    /// - **`constraint: C`** - Accepts any type that can be converted into a **`Constraint<F>`**. Chiquito provides syntax sugar for defining complex constraints. Refer to **Constraint Builder DSL Functions** section for more information.    
    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    /// # **Description:**
    /// Adds a transition constraint to the step type. It’s the same as a regular constraint except that it can involve forward signal(s) as well.
    /// # **Arguments:**
    /// - **`constraint: C`** - Accepts any type that can be converted into a **`Constraint<F>`**. Chiquito provides syntax sugar for defining complex constraints. Refer to **Constraint Builder DSL Functions** section for more information.    
    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    /// # **Description:**
    /// Sets the witness generation function for the step type. The witness generation function is responsible for assigning witness values to witness column **`Queriable`**. It is entirely left for the user to implement and is Turing complete. Users typically generate cell values and call the assign function to fill the witness columns.
    /// # **Arguments:**
    /// - **`def: D`** - The witness generation function, which takes a mutable reference to a **`WitnessGenContext`** and an **`Args`** instance, a generic type representing the arguments passed to the witness generation function. See more information about the **`WitnessGenContext`** trait and its assign function below.
    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

impl<F: Debug + Clone, Args> StepTypeContext<F, Args> {
    /// # **Description:**
    /// Adds a lookup table to the step type.
    /// # **Arguments:**
    /// - **`lookup_builder: &mut LookupBuilder<F>`** - The lookup table builder from which to add the lookup table to the step type.
    pub fn add_lookup(&mut self, lookup_builder: &mut LookupBuilder<F>) {
        self.step_type.lookups.push(lookup_builder.lookup.clone());
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

/// Creates a `Circuit` instance by providing a name and a definition closure that is applied to a mutable `CircuitContext`. The user customizes the definition closure by calling `CircuitContext` functions. This is the main function that users call to define a Chiquito circuit.
/// # **Arguments:**
/// `_name: &str`: The name of the circuit. (Note: Currently, the name is not used for annotation within the function, but it may be used in future implementations.)
/// `def: D`: A closure that defines the circuit by modifying a `CircuitContext`. The closure has the following signature: `Fn(&mut CircuitContext<F, TraceArgs, StepArgs>)`.
/// # **Return:**
/// `Circuit<F, TraceArgs, StepArgs>`: A new Circuit instance, as defined by the provided closure.
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
