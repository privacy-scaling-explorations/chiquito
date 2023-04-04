pub mod expr;

use std::fmt::Debug;
use std::{collections::HashMap, rc::Rc};

use crate::compiler::{FixedGenContext, TraceContext, WitnessGenContext};
use crate::dsl::StepTypeHandler;
use crate::util::uuid;

pub use expr::*;

use halo2_proofs::plonk::{Advice, Column as Halo2Column, ColumnType, Fixed};

/// SuperCircuit
pub struct Circuit<F, TraceArgs, StepArgs> {
    pub forward_signals: Vec<ForwardSignal>,
    pub halo2_advice: Vec<ImportedHalo2Advice>,
    pub halo2_fixed: Vec<ImportedHalo2Fixed>,
    pub step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,
    pub trace: Option<Rc<Trace<TraceArgs, StepArgs>>>,
    pub fixed_gen: Option<Rc<FixedGen<F>>>,

    pub annotations: HashMap<u32, String>,

    pub first_step: Option<StepTypeHandler>,
    pub last_step: Option<StepTypeHandler>,
}

impl<F: Debug, TraceArgs: Debug, StepArgs: Debug> Debug for Circuit<F, TraceArgs, StepArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Circuit")
            .field("forward_signals", &self.forward_signals)
            .field("halo2_advice", &self.halo2_advice)
            .field("step_types", &self.step_types)
            .field("annotations", &self.annotations)
            .finish()
    }
}

impl<F, TraceArgs, StepArgs> Default for Circuit<F, TraceArgs, StepArgs> {
    fn default() -> Self {
        Self {
            forward_signals: Default::default(),
            halo2_advice: Default::default(),
            halo2_fixed: Default::default(),
            step_types: Default::default(),
            trace: None,
            fixed_gen: None,
            annotations: Default::default(),
            first_step: None,
            last_step: None,
        }
    }
}

impl<F, TraceArgs, StepArgs> Circuit<F, TraceArgs, StepArgs> {
    pub fn add_forward(&mut self, name: &str, phase: usize) -> ForwardSignal {
        let signal = ForwardSignal::new_with_phase(phase);

        self.forward_signals.push(signal);
        self.annotations.insert(signal.uuid(), name.to_string());

        signal
    }

    pub fn add_halo2_advice(
        &mut self,
        name: &str,
        column: Halo2Column<Advice>,
    ) -> ImportedHalo2Advice {
        let advice = ImportedHalo2Advice::new(column);

        self.halo2_advice.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_halo2_fixed(
        &mut self,
        name: &str,
        column: Halo2Column<Fixed>,
    ) -> ImportedHalo2Fixed {
        let advice = ImportedHalo2Fixed::new(column);

        self.halo2_fixed.push(advice);
        self.annotations.insert(advice.uuid(), name.to_string());

        advice
    }

    pub fn add_step_type<N: Into<String>>(&mut self, handler: StepTypeHandler, name: N) {
        self.annotations.insert(handler.uuid(), name.into());
    }

    pub fn add_step_type_def(&mut self, step: StepType<F, StepArgs>) -> StepTypeUUID {
        let uuid = step.uuid();
        let step_rc = Rc::new(step);
        self.step_types.insert(uuid, step_rc);

        uuid
    }

    pub fn set_trace<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        match self.trace {
            None => {
                self.trace = Some(Rc::new(def));
            }
            Some(_) => panic!("circuit cannot have more than one trace generator"),
        }
    }

    pub fn set_fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn FixedGenContext<F>) + 'static,
    {
        match self.fixed_gen {
            None => self.fixed_gen = Some(Rc::new(def)),
            Some(_) => panic!("circuit cannot have more than one fixed generator"),
        }
    }

    pub fn get_step_type(&self, uuid: u32) -> Rc<StepType<F, StepArgs>> {
        let step_rc = self.step_types.get(&uuid).expect("step type not found");

        Rc::clone(step_rc)
    }
}

pub type Trace<TraceArgs, StepArgs> = dyn Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static;
pub type FixedGen<F> = dyn Fn(&mut dyn FixedGenContext<F>) + 'static;
pub type StepWitnessGen<F, Args> = dyn Fn(&mut dyn WitnessGenContext<F>, Args) + 'static;

pub type StepTypeUUID = u32;

/// Step
pub struct StepType<F, Args> {
    id: StepTypeUUID,

    pub signals: Vec<InternalSignal>,
    pub constraints: Vec<Constraint<F>>,
    pub transition_constraints: Vec<TransitionConstraint<F>>,
    pub lookups: Vec<Lookup<F>>,
    pub annotations: HashMap<u32, String>,

    pub wg: Box<StepWitnessGen<F, Args>>,
}

impl<F: Debug, Args> Debug for StepType<F, Args> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StepType")
            .field("id", &self.id)
            .field("signals", &self.signals)
            .field("constraints", &self.constraints)
            .field("transition_constraints", &self.transition_constraints)
            .finish()
    }
}

impl<F, Args> Default for StepType<F, Args> {
    fn default() -> Self {
        Self {
            id: uuid(),
            signals: Default::default(),
            constraints: Default::default(),
            transition_constraints: Default::default(),
            lookups: Default::default(),
            annotations: Default::default(),
            wg: Box::new(|_, _| {}),
        }
    }
}

impl<F, Args> StepType<F, Args> {
    pub fn new(uuid: u32) -> Self {
        Self {
            id: uuid,
            signals: Default::default(),
            constraints: Default::default(),
            transition_constraints: Default::default(),
            lookups: Default::default(),
            annotations: Default::default(),
            wg: Box::new(|_, _| {}),
        }
    }
    pub fn uuid(&self) -> StepTypeUUID {
        self.id
    }

    pub fn add_signal<N: Into<String>>(&mut self, name: N) -> InternalSignal {
        let signal = InternalSignal::new();

        self.signals.push(signal);
        self.annotations.insert(signal.uuid(), name.into());

        signal
    }

    pub fn add_constr(&mut self, annotation: &str, expr: Expr<F>) {
        let condition = Constraint {
            annotation: annotation.to_string(),
            expr,
        };

        self.constraints.push(condition)
    }

    pub fn add_transition(&mut self, annotation: &str, expr: Expr<F>) {
        let condition = TransitionConstraint {
            annotation: annotation.to_string(),
            expr,
        };

        self.transition_constraints.push(condition)
    }

    pub fn add_lookup(&mut self, exprs: Vec<(Expr<F>, Expr<F>)>) {
        let lookup = Lookup { exprs };

        self.lookups.push(lookup);
    }

    pub fn set_wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static,
    {
        // TODO, only can be called once
        self.wg = Box::new(def);
    }
}

impl<F, Args> PartialEq for StepType<F, Args> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<F, Args> Eq for StepType<F, Args> {}

impl<F, Args> core::hash::Hash for StepType<F, Args> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Clone, Debug)]
/// Condition
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
}

#[derive(Clone, Debug)]
/// TransitionCondition
pub struct TransitionConstraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
}

pub struct Lookup<F> {
    pub exprs: Vec<(Expr<F>, Expr<F>)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// ForwardSignal
pub struct ForwardSignal {
    id: u32,
    phase: usize,
}

impl ForwardSignal {
    pub fn new_with_phase(phase: usize) -> ForwardSignal {
        ForwardSignal { id: uuid(), phase }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }

    pub fn phase(&self) -> usize {
        self.phase
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InternalSignal {
    id: u32,
}

impl InternalSignal {
    pub fn new() -> InternalSignal {
        InternalSignal { id: uuid() }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ImportedHalo2Column<CT: ColumnType> {
    id: u32,
    pub column: Halo2Column<CT>,
}

impl<CT: ColumnType> ImportedHalo2Column<CT> {
    pub fn new(column: Halo2Column<CT>) -> ImportedHalo2Column<CT> {
        ImportedHalo2Column { id: uuid(), column }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }
}

pub type ImportedHalo2Advice = ImportedHalo2Column<Advice>;
pub type ImportedHalo2Fixed = ImportedHalo2Column<Fixed>;
