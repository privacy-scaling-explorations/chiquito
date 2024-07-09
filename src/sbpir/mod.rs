pub mod query;

use std::{collections::HashMap, fmt::Debug, hash::Hash, rc::Rc};

use crate::{
    field::Field,
    frontend::dsl::{
        trace::{DSLTraceGenerator, TraceContext},
        StepTypeHandler,
    },
    poly::{ConstrDecomp, Expr, Meta, VarAssignments},
    util::{uuid, UUID},
    wit_gen::{FixedAssignment, FixedGenContext, NullTraceGenerator, TraceGenerator},
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, ColumnType, Fixed};

use self::query::Queriable;

/// Circuit (Step-Based Polynomial Identity Representation)
#[derive(Clone)]
pub struct SBPIR<F, TG: TraceGenerator<F> = DSLTraceGenerator<F>, M: Meta = ()> {
    pub step_types: HashMap<UUID, StepType<F, M>>,

    pub forward_signals: Vec<ForwardSignal>,
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,
    pub halo2_advice: Vec<ImportedHalo2Advice>,
    pub halo2_fixed: Vec<ImportedHalo2Fixed>,
    pub exposed: Vec<(Queriable<F>, ExposeOffset)>,

    pub annotations: HashMap<UUID, String>,

    pub trace_generator: Option<TG>,
    pub fixed_assignments: Option<FixedAssignment<F>>,

    pub first_step: Option<StepTypeUUID>,
    pub last_step: Option<StepTypeUUID>,
    pub num_steps: usize,
    pub q_enable: bool,

    pub id: UUID,
}

impl<F: Debug, TG: TraceGenerator<F>, M: Meta> Debug for SBPIR<F, TG, M> {
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

impl<F, TG: TraceGenerator<F>, M: Meta> Default for SBPIR<F, TG, M> {
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

            trace_generator: None,
            fixed_assignments: None,

            first_step: None,
            last_step: None,

            id: uuid(),
            q_enable: true,
        }
    }
}

impl<F, TG: TraceGenerator<F>, M: Meta> SBPIR<F, TG, M> {
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

    pub fn add_step_type_def(&mut self, step: StepType<F, M>) -> StepTypeUUID {
        let uuid = step.uuid();
        self.step_types.insert(uuid, step);

        uuid
    }

    pub fn set_fixed_assignments(&mut self, assignments: FixedAssignment<F>) {
        match self.fixed_assignments {
            None => {
                self.fixed_assignments = Some(assignments);
            }
            Some(_) => panic!("circuit cannot have more than one fixed generator"),
        }
    }

    pub fn without_trace(self) -> SBPIR<F, NullTraceGenerator, M> {
        SBPIR {
            step_types: self.step_types,
            forward_signals: self.forward_signals,
            shared_signals: self.shared_signals,
            fixed_signals: self.fixed_signals,
            halo2_advice: self.halo2_advice,
            halo2_fixed: self.halo2_fixed,
            exposed: self.exposed,
            annotations: self.annotations,
            trace_generator: None, // Remove the trace.
            fixed_assignments: self.fixed_assignments,
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }

    pub(crate) fn with_trace<TG2: TraceGenerator<F>>(self, trace: TG2) -> SBPIR<F, TG2, M> {
        SBPIR {
            trace_generator: Some(trace), // Change trace
            step_types: self.step_types,
            forward_signals: self.forward_signals,
            shared_signals: self.shared_signals,
            fixed_signals: self.fixed_signals,
            halo2_advice: self.halo2_advice,
            halo2_fixed: self.halo2_fixed,
            exposed: self.exposed,
            annotations: self.annotations,
            fixed_assignments: self.fixed_assignments,
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

impl<F: Field + Hash, TG: TraceGenerator<F> + Clone, M: Meta> SBPIR<F, TG, M> {
    pub fn with_meta<N: Meta>(
        &self,
        assignments: &VarAssignments<F, Queriable<F>>,
    ) -> SBPIR<F, TG, N> {
        SBPIR {
            step_types: self
                .step_types
                .iter()
                .map(|(k, v)| (*k, v.with_meta(assignments)))
                .collect(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace_generator: self.trace_generator.clone(),
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

impl<F: Field + Hash, TG: TraceGenerator<F> + Clone, M: Meta> SBPIR<F, TG, M> {
    pub fn without_meta(&self) -> SBPIR<F, TG, ()> {
        SBPIR {
            step_types: self
                .step_types
                .iter()
                .map(|(k, v)| (*k, v.without_meta()))
                .collect(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace_generator: self.trace_generator.clone(),
            fixed_assignments: self.fixed_assignments.clone(),
            first_step: self.first_step,
            last_step: self.last_step,
            num_steps: self.num_steps,
            q_enable: self.q_enable,
            id: self.id,
        }
    }
}

impl<F: Field, TraceArgs: Clone> SBPIR<F, DSLTraceGenerator<F, TraceArgs>> {
    pub fn set_trace<D>(&mut self, def: D)
    where
        D: Fn(&mut TraceContext<F>, TraceArgs) + 'static,
    {
        // TODO: should we check that number of steps has been set?

        match self.trace_generator {
            None => {
                self.trace_generator = Some(DSLTraceGenerator::new(Rc::new(def), self.num_steps));
            }
            Some(_) => panic!("circuit cannot have more than one trace generator"),
        }
    }
}

impl<F: Clone + Field, TG: TraceGenerator<F>> SBPIR<F, TG> {
    pub fn clone_without_trace(&self) -> SBPIR<F, NullTraceGenerator> {
        SBPIR {
            step_types: self.step_types.clone(),
            forward_signals: self.forward_signals.clone(),
            shared_signals: self.shared_signals.clone(),
            fixed_signals: self.fixed_signals.clone(),
            halo2_advice: self.halo2_advice.clone(),
            halo2_fixed: self.halo2_fixed.clone(),
            exposed: self.exposed.clone(),
            annotations: self.annotations.clone(),
            trace_generator: None, // Remove the trace.
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

#[derive(Clone)]
/// Step
pub struct StepType<F, M: Meta> {
    id: StepTypeUUID,

    pub name: String,
    pub signals: Vec<InternalSignal>,
    pub constraints: Vec<Constraint<F, M>>,
    pub transition_constraints: Vec<TransitionConstraint<F, M>>,
    pub lookups: Vec<Lookup<F, M>>,

    pub auto_signals: HashMap<Queriable<F>, PIR<F, M>>,

    pub annotations: HashMap<UUID, String>,
}

impl<F: Debug, M: Meta> Debug for StepType<F, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StepType")
            .field("id", &self.id)
            .field("signals", &self.signals)
            .field("constraints", &self.constraints)
            .field("transition_constraints", &self.transition_constraints)
            .field("lookups", &self.lookups)
            .field("auto_signals", &self.auto_signals)
            .finish()
    }
}

impl<F, M: Meta> StepType<F, M> {
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
        let signal = InternalSignal::new(name);

        self.add_internal(signal);

        signal
    }

    fn add_internal(&mut self, signal: InternalSignal) {
        self.annotations
            .insert(signal.uuid(), signal.annotation.to_string());
        self.signals.push(signal);
    }

    pub fn add_constr(&mut self, annotation: String, expr: PIR<F, M>) {
        let condition = Constraint { annotation, expr };

        self.constraints.push(condition)
    }

    pub fn add_transition(&mut self, annotation: String, expr: PIR<F, M>) {
        let condition = TransitionConstraint { annotation, expr };

        self.transition_constraints.push(condition)
    }
}

impl<F: Field + Hash, M: Meta> StepType<F, M> {
    pub fn with_meta<N: Meta>(
        &self,
        assignments: &VarAssignments<F, Queriable<F>>,
    ) -> StepType<F, N> {
        StepType {
            id: self.id,
            name: self.name.clone(),
            signals: self.signals.clone(),
            constraints: self
                .constraints
                .iter()
                .map(|c| c.with_meta(assignments))
                .collect(),
            transition_constraints: self
                .transition_constraints
                .iter()
                .map(|c| c.with_meta(assignments))
                .collect(),
            lookups: self
                .lookups
                .iter()
                .map(|l| l.with_meta(assignments))
                .collect(),
            auto_signals: self
                .auto_signals
                .iter()
                .map(|(k, v)| (*k, v.with_meta(assignments)))
                .collect(),
            annotations: self.annotations.clone(),
        }
    }
}

impl<F: Field + Hash, M: Meta> StepType<F, M> {
    pub fn without_meta(&self) -> StepType<F, ()> {
        StepType {
            id: self.id,
            name: self.name.clone(),
            signals: self.signals.clone(),
            constraints: self.constraints.iter().map(|c| c.without_meta()).collect(),
            transition_constraints: self
                .transition_constraints
                .iter()
                .map(|c| c.without_meta())
                .collect(),
            lookups: self.lookups.iter().map(|l| l.without_meta()).collect(),
            auto_signals: self
                .auto_signals
                .iter()
                .map(|(k, v)| (*k, v.without_meta()))
                .collect(),
            annotations: self.annotations.clone(),
        }
    }
}

impl<F: Clone + Eq + Hash, M: Meta> StepType<F, M> {
    pub fn decomp_constraints<D>(&mut self, mut decomposer: D)
    where
        D: FnMut(
            &Expr<F, Queriable<F>, M>,
        ) -> (Expr<F, Queriable<F>, M>, ConstrDecomp<F, Queriable<F>, M>),
    {
        let mut new_constraints = vec![];
        for i in 0..self.constraints.len() {
            let decomp = decomposer(&self.constraints[i].expr);

            self.constraints[i].expr = decomp.0;

            decomp.1.constrs.iter().for_each(|expr| {
                new_constraints.push(Constraint {
                    annotation: self.constraints[i].annotation.clone(),
                    expr: expr.clone(),
                });
            });

            decomp.1.auto_signals.into_iter().for_each(|(q, expr)| {
                if let Queriable::Internal(signal) = q {
                    self.add_internal(signal);
                } else {
                    unreachable!("should use internal signals");
                }

                self.auto_signals.insert(q, expr);
            });
        }

        self.constraints.extend(new_constraints);

        let mut new_constraints = vec![];
        for i in 0..self.transition_constraints.len() {
            let decomp = decomposer(&self.constraints[i].expr);

            self.transition_constraints[i].expr = decomp.0;

            decomp.1.constrs.iter().for_each(|expr| {
                new_constraints.push(TransitionConstraint {
                    annotation: self.constraints[i].annotation.clone(),
                    expr: expr.clone(),
                });
            });

            decomp.1.auto_signals.into_iter().for_each(|(q, expr)| {
                if let Queriable::Internal(signal) = q {
                    self.add_internal(signal);
                } else {
                    unreachable!("should use internal signals");
                }

                self.auto_signals.insert(q, expr);
            });
        }
        self.transition_constraints.extend(new_constraints);
    }
}

impl<F, M: Meta> PartialEq for StepType<F, M> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<F, M: Meta> Eq for StepType<F, M> {}

impl<F, M: Meta> core::hash::Hash for StepType<F, M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

pub type PIR<F, M> = Expr<F, Queriable<F>, M>;

#[derive(Clone, Debug)]
/// Condition
pub struct Constraint<F, M: Meta> {
    pub annotation: String,
    pub expr: PIR<F, M>,
}

impl<F: Field + Hash, M: Meta> Constraint<F, M> {
    pub fn with_meta<N: Meta>(
        &self,
        assignments: &VarAssignments<F, Queriable<F>>,
    ) -> Constraint<F, N> {
        Constraint {
            annotation: self.annotation.clone(),
            expr: self.expr.with_meta(assignments),
        }
    }
}

impl<F: Field, M: Meta> Constraint<F, M> {
    pub fn without_meta(&self) -> Constraint<F, ()> {
        Constraint {
            annotation: self.annotation.clone(),
            expr: self.expr.without_meta(),
        }
    }
}

#[derive(Clone, Debug)]
/// TransitionCondition
pub struct TransitionConstraint<F, M: Meta> {
    pub annotation: String,
    pub expr: PIR<F, M>,
}

impl<F: Field + Hash, M: Meta> TransitionConstraint<F, M> {
    pub fn with_meta<N: Meta>(
        &self,
        assignments: &VarAssignments<F, Queriable<F>>,
    ) -> TransitionConstraint<F, N> {
        TransitionConstraint {
            annotation: self.annotation.clone(),
            expr: self.expr.with_meta(assignments),
        }
    }
}

impl<F: Field, M: Meta> TransitionConstraint<F, M> {
    pub fn without_meta(&self) -> TransitionConstraint<F, ()> {
        TransitionConstraint {
            annotation: self.annotation.clone(),
            expr: self.expr.without_meta(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lookup<F, M: Meta> {
    pub annotation: String,
    pub exprs: Vec<(Constraint<F, M>, PIR<F, M>)>,
    pub enable: Option<Constraint<F, M>>,
}

impl<F, M: Meta> Default for Lookup<F, M> {
    fn default() -> Self {
        Lookup {
            annotation: String::new(),
            exprs: Vec::<(Constraint<F, M>, PIR<F, M>)>::new(),
            enable: None,
        }
    }
}

impl<F: Debug + Clone, M: Meta> Lookup<F, M> {
    // Function: adds (constraint, expression) to exprs if there's no enabler, OR add (enabler *
    // constraint, expression) to exprs if there's enabler Note that constraint_annotation and
    // constraint_expr are passed in as separate parameters, and then reconstructed as Constraint,
    // because dsl uses cb::Constraint while ast uses ast::Constraint
    pub fn add(
        &mut self,
        constraint_annotation: String,
        constraint_expr: PIR<F, M>,
        expression: PIR<F, M>,
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
    pub fn enable(&mut self, enable_annotation: String, enable_expr: PIR<F, M>) {
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
    fn multiply_constraints(
        enable: Constraint<F, M>,
        constraint: Constraint<F, M>,
    ) -> Constraint<F, M> {
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

impl<F: Field + Hash, M: Meta> Lookup<F, M> {
    pub fn with_meta<N: Meta>(
        &self,
        assignments: &VarAssignments<F, Queriable<F>>,
    ) -> Lookup<F, N> {
        Lookup {
            annotation: self.annotation.clone(),
            exprs: self
                .exprs
                .iter()
                .map(|(c, e)| (c.with_meta(assignments), e.with_meta(assignments)))
                .collect(),
            enable: self.enable.as_ref().map(|e| e.with_meta(assignments)),
        }
    }
}

impl<F: Field, M: Meta> Lookup<F, M> {
    pub fn without_meta(&self) -> Lookup<F, ()> {
        Lookup {
            annotation: self.annotation.clone(),
            exprs: self
                .exprs
                .iter()
                .map(|(c, e)| (c.without_meta(), e.without_meta()))
                .collect(),
            enable: self.enable.as_ref().map(|e| e.without_meta()),
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
    pub fn new<S: Into<String>>(annotation: S) -> ForwardSignal {
        Self::new_with_id(uuid(), 0, annotation.into())
    }

    pub fn new_with_phase<S: Into<String>>(phase: usize, annotation: S) -> ForwardSignal {
        ForwardSignal {
            id: uuid(),
            phase,
            annotation: Box::leak(annotation.into().into_boxed_str()),
        }
    }

    pub fn new_with_id<S: Into<String>>(id: UUID, phase: usize, annotation: S) -> Self {
        Self {
            id,
            phase,
            annotation: Box::leak(annotation.into().into_boxed_str()),
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
    pub fn new_with_phase<S: Into<String>>(phase: usize, annotation: S) -> SharedSignal {
        SharedSignal {
            id: uuid(),
            phase,
            annotation: Box::leak(annotation.into().into_boxed_str()),
        }
    }

    pub fn new_with_id<S: Into<String>>(id: UUID, phase: usize, annotation: S) -> Self {
        Self {
            id,
            phase,
            annotation: Box::leak(annotation.into().into_boxed_str()),
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
    pub fn new<S: Into<String>>(annotation: S) -> FixedSignal {
        FixedSignal {
            id: uuid(),
            annotation: Box::leak(annotation.into().into_boxed_str()),
        }
    }

    pub fn new_with_id<S: Into<String>>(id: UUID, annotation: S) -> Self {
        Self {
            id,
            annotation: Box::leak(annotation.into().into_boxed_str()),
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

    pub fn new_with_id<S: Into<String>>(id: UUID, annotation: S) -> Self {
        Self {
            id,
            annotation: Box::leak(annotation.into().into_boxed_str()),
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
    use crate::wit_gen::NullTraceGenerator;

    use super::*;

    #[test]
    fn test_q_enable() {
        let circuit: SBPIR<i32, NullTraceGenerator> = SBPIR::default();
        assert!(circuit.q_enable);
    }

    #[test]
    #[should_panic]
    fn test_expose_non_existing_signal() {
        let mut circuit: SBPIR<i32, NullTraceGenerator> = SBPIR::default();
        let signal = Queriable::Forward(
            ForwardSignal::new_with_phase(0, "signal".to_string()),
            false,
        );
        let offset = ExposeOffset::First;

        circuit.expose(signal, offset);
    }

    #[test]
    fn test_expose_forward_signal() {
        let mut circuit: SBPIR<i32, NullTraceGenerator> = SBPIR::default();
        let signal = circuit.add_forward("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Forward(signal, false), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }

    #[test]
    fn test_expose_shared_signal() {
        let mut circuit: SBPIR<i32, NullTraceGenerator> = SBPIR::default();
        let signal = circuit.add_shared("signal", 0);
        let offset = ExposeOffset::Last;
        assert_eq!(circuit.exposed.len(), 0);
        circuit.expose(Queriable::Shared(signal, 10), offset);
        assert_eq!(circuit.exposed.len(), 1);
    }
}
