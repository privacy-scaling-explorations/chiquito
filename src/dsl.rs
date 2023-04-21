use crate::{
    ast::{query::Queriable, Circuit, Expr, StepType, StepTypeUUID, Lookup},
    compiler::{FixedGenContext, TraceContext, WitnessGenContext},
    util::uuid,
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use core::fmt::Debug;

use self::cb::{Constraint, LookupBuilder};

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
        let mut context =
            StepTypeContext::<F, StepArgs>::new(handler.uuid(), handler.annotation.to_string());

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

impl<F, Args> StepTypeContext<F, Args> {
    pub fn new(uuid: u32, name: String) -> Self {
        Self {
            step_type: StepType::new(uuid, name),
        }
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

    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

impl<F: Debug + Clone, Args> StepTypeContext<F, Args> {
    // Function: add Lookup in LookupBuilder to StepType
    // Usage: ctx.add_lookup(lookup().add(...).add(...).enable(...))
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
