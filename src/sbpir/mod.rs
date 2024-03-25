pub mod query;

use std::{collections::HashMap, fmt::Debug, hash::Hash, rc::Rc};

use crate::{
    frontend::dsl::StepTypeHandler,
    poly::Expr,
    util::{uuid, UUID},
    wit_gen::{FixedAssignment, FixedGenContext, Trace, TraceContext},
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, ColumnType, Fixed};

use self::query::Queriable;

/// Circuit
#[derive(Clone)]
pub struct SBPIR<F, TraceArgs> {
    pub step_types: HashMap<UUID, Rc<StepType<F>>>,

    pub forward_signals: Vec<ForwardSignal>,
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,
    pub halo2_advice: Vec<ImportedHalo2Advice>,
    pub halo2_fixed: Vec<ImportedHalo2Fixed>,
    pub exposed: Vec<(Queriable<F>, ExposeOffset)>,

    pub annotations: HashMap<UUID, String>,

    pub trace: Option<Rc<Trace<F, TraceArgs>>>,
    pub fixed_assignments: Option<FixedAssignment<F>>,

    pub first_step: Option<StepTypeUUID>,
    pub last_step: Option<StepTypeUUID>,
    pub num_steps: usize,
    pub q_enable: bool,

    pub id: UUID,
}

impl<F: Debug, TraceArgs: Debug> Debug for SBPIR<F, TraceArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Circuit")
            .field("step_types", &self.step_types)
            .field("forward_signals", &self.forward_signals)
            .field("shared_signals", &self.shared_signals)
            .field("fixed_signals", &self.fixed_signals)
            .field("halo2_advice", &self.halo2_advice)
            .field("halo2_fixed", &self.halo2_fixed)
            .field("exposed", &self.exposed)
            .field("annotations", &self.annotations)
            .field("fixed_assignments", &self.fixed_assignments)
            .field("first_step", &self.first_step)
            .field("last_step", &self.last_step)
            .field("num_steps", &self.num_steps)
            .field("q_enable", &self.q_enable)
            .finish()
    }
}

impl<F, TraceArgs> Default for SBPIR<F, TraceArgs> {
    fn default() -> Self {
        Self {
            step_types: Default::default(),
            forward_signals: Default::default(),
            shared_signals: Default::default(),
            fixed_signals: Default::default(),
            halo2_advice: Default::default(),
            halo2_fixed: Default::default(),
            exposed: Default::default(),

            num_steps: Default::default(),

            annotations: Default::default(),

            trace: None,
            fixed_assignments: None,

            first_step: None,
            last_step: None,

            id: uuid(),
            q_enable: true,
        }
    }
}

impl<F, TraceArgs> SBPIR<F, TraceArgs> {
    pub fn add_forward<N: Into<String>>(&mut self, name: N, phase: usize) -> ForwardSignal {
        let name = name.into();
        let signal = ForwardSignal::new_with_phase(phase, name.clone());

        self.forward_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    pub fn add_shared<N: Into<String>>(&mut self, name: N, phase: usize) -> SharedSignal {
        let name = name.into();
        let signal = SharedSignal::new_with_phase(phase, name.clone());

        self.shared_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    pub fn add_fixed<N: Into<String>>(&mut self, name: N) -> FixedSignal {
        let name = name.into();
        let signal = FixedSignal::new(name.clone());

        self.fixed_signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    pub fn expose(&mut self, signal: Queriable<F>, offset: ExposeOffset) {
        match signal {
            Queriable::Forward(..) | Queriable::Shared(..) => {
                let existing_forward_signal = self
                    .forward_signals
                    .clone()
                    .iter()
                    .any(|s| s.uuid() == signal.uuid());
                let existing_shared_signal = self
                    .shared_signals
                    .clone()
                    .iter()
                    .any(|s| s.uuid() == signal.uuid());
                if !existing_forward_signal && !existing_shared_signal {
                    panic!("Signal not found in forward signals.");
                }
                self.exposed.push((signal, offset));
            }
            _ => panic!("Can only expose forward and shared signals."),
        }
    }

    pub fn add_halo2_advice(
        &mut self,
        name: &str,
        column: Halo2Column<Advice>,
    ) -> ImportedHalo2Advice {
        let advice = ImportedHalo2Advice::new(column, name.to_string());

        self.halo2_advice.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_halo2_fixed(
        &mut self,
        name: &str,
        column: Halo2Column<Fixed>,
    ) -> ImportedHalo2Fixed {
        let advice = ImportedHalo2Fixed::new(column, name.to_string());

        self.halo2_fixed.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_step_type<N: Into<String>>(&mut self, handler: StepTypeHandler, name: N) {
        self.annotations.insert(handler.uuid(), name.into());
    }

    pub fn add_step_type_def(&mut self, step: StepType<F>) -> StepTypeUUID {
        let uuid = step.uuid();
        let step_rc = Rc::new(step);
        self.step_types.insert(uuid, step_rc);

        uuid
    }

    pub fn set_trace<D>(&mut self, def: D)
    where
        D: Fn(&mut TraceContext<F>, TraceArgs) + 'static,
    {
        match self.trace {
            None => {
                self.trace = Some(Rc::new(def));
            }
            Some(_) => panic!("circuit cannot have more than one trace generator"),
        }
    }

    pub fn get_step_type(&self, uuid: UUID) -> Rc<StepType<F>> {
        let step_rc = self.step_types.get(&uuid).expect("step type not found");

        Rc::clone(step_rc)
    }

    pub fn set_fixed_assignments(&mut self, assignments: FixedAssignment<F>) {
        match self.fixed_assignments {
            None => {
                self.fixed_assignments = Some(assignments);
            }
            Some(_) => panic!("circuit cannot have more than one fixed generator"),
        }
    }
}

impl<F: Clone, TraceArgs> SBPIR<F, TraceArgs> {
    pub fn clone_without_trace(&self) -> SBPIR<F, ()> {
        SBPIR {
            step_types: self.step_types.clone(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace: None, // Remove the trace.
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

pub type FixedGen<F> = dyn Fn(&mut FixedGenContext<F>) + 'static;

pub type StepTypeUUID = UUID;

/// Step
pub struct StepType<F> {
    id: StepTypeUUID,

    pub name: String,
    pub signals: Vec<InternalSignal>,
    pub constraints: Vec<Constraint<F>>,
    pub transition_constraints: Vec<TransitionConstraint<F>>,
    pub lookups: Vec<Lookup<F>>,

    pub auto_signals: HashMap<Queriable<F>, PIR<F>>,

    pub annotations: HashMap<UUID, String>,
}

impl<F: Debug> Debug for StepType<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StepType")
            .field("id", &self.id)
            .field("signals", &self.signals)
            .field("constraints", &self.constraints)
            .field("transition_constraints", &self.transition_constraints)
            .field("lookups", &self.lookups)
            .finish()
    }
}

impl<F> StepType<F> {
    pub fn new(uuid: UUID, name: String) -> Self {
        Self {
            id: uuid,
            name,
            signals: Default::default(),
            constraints: Default::default(),
            transition_constraints: Default::default(),
            lookups: Default::default(),
            auto_signals: Default::default(),
            annotations: Default::default(),
        }
    }

    pub fn uuid(&self) -> StepTypeUUID {
        self.id
    }

    pub fn name(&self) -> String {
        self.name.clone()
    }

    pub fn add_signal<N: Into<String>>(&mut self, name: N) -> InternalSignal {
        let name = name.into();
        let signal = InternalSignal::new(name.clone());

        self.signals.push(signal);
        self.annotations.insert(signal.uuid(), name);

        signal
    }

    pub fn add_constr(&mut self, annotation: String, expr: PIR<F>) {
        let condition = Constraint { annotation, expr };

        self.constraints.push(condition)
    }

    pub fn add_transition(&mut self, annotation: String, expr: PIR<F>) {
        let condition = TransitionConstraint { annotation, expr };

        self.transition_constraints.push(condition)
    }
}

impl<F> PartialEq for StepType<F> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<F> Eq for StepType<F> {}

impl<F> core::hash::Hash for StepType<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

pub type PIR<F> = Expr<F, Queriable<F>>;

#[derive(Clone, Debug)]
/// Condition
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: PIR<F>,
}

#[derive(Clone, Debug)]
/// TransitionCondition
pub struct TransitionConstraint<F> {
    pub annotation: String,
    pub expr: PIR<F>,
}

#[derive(Clone, Debug)]
pub struct Lookup<F> {
    pub annotation: String,
    pub exprs: Vec<(Constraint<F>, PIR<F>)>,
    pub enable: Option<Constraint<F>>,
}

impl<F> Default for Lookup<F> {
    fn default() -> Self {
        Lookup {
            annotation: String::new(),
            exprs: Vec::<(Constraint<F>, PIR<F>)>::new(),
            enable: None,
        }
    }
}

impl<F: Debug + Clone> Lookup<F> {
    // Function: adds (constraint, expression) to exprs if there's no enabler, OR add (enabler *
    // constraint, expression) to exprs if there's enabler Note that constraint_annotation and
    // constraint_expr are passed in as separate parameters, and then reconstructed as Constraint,
    // because dsl uses cb::Constraint while ast uses ast::Constraint
    pub fn add(
        &mut self,
        constraint_annotation: String,
        constraint_expr: PIR<F>,
        expression: PIR<F>,
    ) {
        let constraint = Constraint {
            annotation: constraint_annotation,
            expr: constraint_expr,
        };
        self.annotation += &format!("match({} => {:?}) ", &constraint.annotation, &expression); // expression: Expr<F> is formatted using the fmt method defined in the Debug trait
        match self.enable {
            None => {
                self.exprs.push((constraint, expression));
            }
            Some(_) => {
                self.exprs.push((
                    Self::multiply_constraints(self.enable.clone().unwrap(), constraint),
                    expression,
                ));
            }
        }
    }

    // Function: setup the enabler field and multiply all LHS constraints by the enabler if there's
    // no enabler, OR panic if there's an enabler already
    pub fn enable(&mut self, enable_annotation: String, enable_expr: PIR<F>) {
        let enable = Constraint {
            annotation: enable_annotation.clone(),
            expr: enable_expr,
        };
        match self.enable {
            None => {
                // Multiply all LHS constraints by the enabler
                for (constraint, _) in &mut self.exprs {
                    *constraint = Self::multiply_constraints(enable.clone(), constraint.clone());
                }
                self.enable = Some(enable);
                self.annotation = format!("if {}, ", enable_annotation) + &self.annotation;
            }
            Some(_) => panic!("Enable constraint already exists"),
        }
    }

    // Function: helper function for multiplying enabler to constraint
    fn multiply_constraints(enable: Constraint<F>, constraint: Constraint<F>) -> Constraint<F> {
        Constraint {
            annotation: constraint.annotation.clone(), /* annotation only takes the constraint's
                                                        * annotation, because enabler's
                                                        * annotation is already included in the
                                                        * enable function above in the format of
                                                        * "if {enable}" */
            expr: enable.expr * constraint.expr,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// ForwardSignal
pub struct ForwardSignal {
    id: UUID,
    phase: usize,
    annotation: &'static str,
}

impl ForwardSignal {
    pub fn new_with_phase(phase: usize, annotation: String) -> ForwardSignal {
        ForwardSignal {
            id: uuid(),
            phase,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn new_with_id(id: UUID, phase: usize, annotation: String) -> Self {
        Self {
            id,
            phase,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }

    pub fn phase(&self) -> usize {
        self.phase
    }

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SharedSignal {
    id: UUID,
    phase: usize,
    annotation: &'static str,
}

impl SharedSignal {
    pub fn new_with_phase(phase: usize, annotation: String) -> SharedSignal {
        SharedSignal {
            id: uuid(),
            phase,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn new_with_id(id: UUID, phase: usize, annotation: String) -> Self {
        Self {
            id,
            phase,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }

    pub fn phase(&self) -> usize {
        self.phase
    }

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FixedSignal {
    id: UUID,
    annotation: &'static str,
}

impl FixedSignal {
    pub fn new(annotation: String) -> FixedSignal {
        FixedSignal {
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

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ExposeOffset {
    First,
    Last,
    Step(usize),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InternalSignal {
    id: UUID,
    annotation: &'static str,
}

impl InternalSignal {
    pub fn new<S: Into<String>>(annotation: S) -> InternalSignal {
        InternalSignal {
            id: uuid(),
            annotation: Box::leak(annotation.into().into_boxed_str()),
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

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ImportedHalo2Column<CT: ColumnType> {
    id: UUID,
    pub column: Halo2Column<CT>,
    annotation: &'static str,
}

impl<CT: ColumnType> ImportedHalo2Column<CT> {
    pub fn new(column: Halo2Column<CT>, annotation: String) -> ImportedHalo2Column<CT> {
        ImportedHalo2Column {
            id: uuid(),
            column,
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }
}

pub type ImportedHalo2Advice = ImportedHalo2Column<Advice>;
pub type ImportedHalo2Fixed = ImportedHalo2Column<Fixed>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_q_enable() {
        let circuit: SBPIR<i32, i32> = SBPIR::default();
        assert!(circuit.q_enable);
    }

    #[test]
    #[should_panic]
    fn test_expose_non_existing_signal() {
        let mut circuit: SBPIR<i32, i32> = SBPIR::default();
        let signal = Queriable::Forward(
            ForwardSignal::new_with_phase(0, "signal".to_string()),
            false,
        );
        let offset = ExposeOffset::First;

        circuit.expose(signal, offset);
    }

    #[test]
    fn test_expose_forward_signal() {
        let mut circuit: SBPIR<i32, i32> = SBPIR::default();
        let signal = circuit.add_forward("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Forward(signal, false), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }

    #[test]
    fn test_expose_shared_signal() {
        let mut circuit: SBPIR<i32, i32> = SBPIR::default();
        let signal = circuit.add_shared("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Shared(signal, 10), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }
}
