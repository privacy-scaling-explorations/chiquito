use crate::{
    ast::{query::Queriable, Circuit, Expr, StepType, StepTypeUUID},
    compiler::{FixedGenContext, TraceContext, WitnessGenContext},
    util::uuid,
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use self::cb::Constraint;

pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: Circuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, 0), false)
    }

    pub fn forward_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, phase), false)
    }

    pub fn import_halo2_advice(&mut self, name: &str, column: Halo2Column<Advice>) -> Queriable<F> {
        Queriable::Halo2AdviceQuery(self.sc.add_halo2_advice(name, column), 0)
    }

    pub fn import_halo2_fixed(&mut self, name: &str, column: Halo2Column<Fixed>) -> Queriable<F> {
        Queriable::Halo2FixedQuery(self.sc.add_halo2_fixed(name, column), 0)
    }

    pub fn step_type(&mut self, name: &str) -> StepTypeHandler {
        let handler = StepTypeHandler::new(name.to_string());

        self.sc.add_step_type(handler, name);

        handler
    }

    pub fn step_type_def<D>(&mut self, handler: StepTypeHandler, def: D)
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context = StepTypeContext::<F, StepArgs>::new(handler.uuid());

        def(&mut context);

        self.sc.add_step_type_def(context.step_type);
    }

    pub fn trace<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
    }

    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn FixedGenContext<F>) + 'static,
    {
        self.sc.set_fixed_gen(def);
    }

    pub fn pragma_first_step(&mut self, step_type: StepTypeHandler) {
        self.sc.first_step = Some(step_type);
    }

    pub fn pragma_last_step(&mut self, step_type: StepTypeHandler) {
        self.sc.last_step = Some(step_type);
    }
}

pub struct StepTypeContext<F, Args> {
    step_type: StepType<F, Args>,
}

impl<F, Args> Default for StepTypeContext<F, Args> {
    fn default() -> Self {
        Self {
            step_type: StepType::default(),
        }
    }
}

impl<F, Args> StepTypeContext<F, Args> {
    pub fn new(uuid: u32) -> Self {
        Self {
            step_type: StepType::new(uuid),
        }
    }

    pub fn signal(&mut self, name: &str) -> Queriable<F> {
        eprintln!("WARN: .signal is deprecated, use .internal instead");
        self.internal(name)
    }

    pub fn internal(&mut self, name: &str) -> Queriable<F> {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    pub fn lookup(&mut self, _annotation: &str, exprs: Vec<(Expr<F>, Expr<F>)>) {
        // TODO annotate lookup
        self.step_type.add_lookup(exprs)
    }

    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

impl<F: Clone, Args> StepTypeContext<F, Args> {
    pub fn transition_to<C: Into<Constraint<F>>>(
        &mut self,
        step_type: StepTypeHandler,
        constraint: C,
    ) {
        let constraint = constraint.into();

        let annotation = format!(
            "if(next step is {})then({})",
            step_type.annotation, constraint.annotation
        );

        self.step_type
            .add_transition(annotation, step_type.next() * constraint.expr);
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
