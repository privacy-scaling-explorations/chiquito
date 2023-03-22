pub mod expr;

use std::rc::Rc;

use std::fmt::Debug;

use crate::{
    compiler::{TraceContext, WitnessGenContext},
    util::uuid,
};

pub type Trace<TraceArgs, StepArgs> = dyn FnOnce(&TraceContext<StepArgs>, TraceArgs);

pub use expr::*;

/// SuperCircuit
pub struct SuperCircuit<F, TraceArgs, StepArgs> {
    pub forward_signals: Vec<ForwardSignal>,
    pub step_types: Vec<Rc<StepType<F, StepArgs>>>,
    pub trace: Option<Box<Trace<TraceArgs, StepArgs>>>,
}

impl<F, TraceArgs, StepArgs> Default for SuperCircuit<F, TraceArgs, StepArgs> {
    fn default() -> Self {
        Self {
            forward_signals: Default::default(),
            step_types: Default::default(),
            trace: None,
        }
    }
}

impl<F, TraceArgs, StepArgs> SuperCircuit<F, TraceArgs, StepArgs> {
    pub fn add_forward(&mut self, name: &str) -> ForwardSignal {
        let signal = ForwardSignal::new();

        self.forward_signals.push(signal);

        signal
    }

    pub fn add_step_type(&mut self, step: StepType<F, StepArgs>) -> Rc<StepType<F, StepArgs>> {
        let step_rc = Rc::new(step);
        self.step_types.push(Rc::clone(&step_rc));

        step_rc
    }

    pub fn set_trace<D>(&mut self, def: D)
    where
        D: FnOnce(&TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        match self.trace {
            None => {
                self.trace = Some(Box::new(def));
            }
            Some(_) => panic!("circuit cannot have more than one trace generator"),
        }
    }
}

type StepTypeUUID = u32;

/// Step
pub struct StepType<F, Args> {
    id: u32,

    pub signals: Vec<InternalSignal>,
    pub constraints: Vec<Constraint<F>>,
    pub transition_constraints: Vec<TransitionConstraint<F>>,

    pub wg: Box<dyn Fn(&WitnessGenContext<F>, Args)>,
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
            wg: Box::new(|_, _| {}),
        }
    }
}

impl<F, Args> StepType<F, Args> {
    pub fn uuid(&self) -> StepTypeUUID {
        self.id
    }

    pub fn add_signal(&mut self, name: &str) -> InternalSignal {
        let signal = InternalSignal::new();

        self.signals.push(signal);

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

    pub fn set_wg<D>(&mut self, def: D)
    where
        D: Fn(&WitnessGenContext<F>, Args) + 'static,
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
    annotation: String,
    expr: Expr<F>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// ForwardSignal
pub struct ForwardSignal {
    id: u32,
}

impl ForwardSignal {
    pub fn new() -> ForwardSignal {
        ForwardSignal { id: uuid() }
    }

    pub fn uuid(&self) -> u32 {
        self.id
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
}
