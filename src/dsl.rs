use crate::{
    ast::{lookup::LookupTable, query::Queriable, Circuit, Expr, StepType, StepTypeUUID},
    compiler::{LookupWitnessGenContext, TraceContext, WitnessGenContext},
};

pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: Circuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name))
    }

    pub fn step_type<D>(&mut self, name: &str, def: D) -> StepTypeHandler
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context = StepTypeContext::<F, StepArgs>::default();

        def(&mut context);

        let step_uuid = self.sc.add_step_type(context.step_type);

        // TODO meaningful StepTypeHandler
        StepTypeHandler::new(step_uuid)
    }

    pub fn trace<D>(&mut self, def: D)
    where
        D: FnOnce(&TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
    }
}

pub struct LookupTableContext<F> {
    table: LookupTable<F>,
}

impl<F> LookupTableContext<F> {
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.table.add_signal(name))
    }

    pub fn constr(&mut self, annotation: &str, expr: Expr<F>) {
        self.table.add_constr(annotation, expr);
    }

    pub fn wg<D, Args>(&mut self, def: D)
    where
        D: FnOnce(&LookupTableContext<F>, Args) + 'static,
    {
        todo!()
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
    pub fn signal(&mut self, name: &str) -> Queriable<F> {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    pub fn constr(&mut self, annotation: &str, expr: Expr<F>) {
        self.step_type.add_constr(annotation, expr);
    }

    pub fn transition<D: Into<Expr<F>>>(&mut self, annotation: &str, expr: D) {
        self.step_type.add_transition(annotation, expr.into());
    }

    pub fn lookup<D: Into<Expr<F>>>(&mut self, exprs: Vec<(D, D)>) {
        let exprs: Vec<(Expr<F>, Expr<F>)> = exprs
            .into_iter()
            .map(|(a, b)| (a.into(), b.into()))
            .collect();

        self.step_type.add_lookup(exprs)
    }

    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StepTypeHandler {
    step_uuid: StepTypeUUID,
}

impl StepTypeHandler {
    pub(crate) fn new(step_uuid: StepTypeUUID) -> StepTypeHandler {
        StepTypeHandler { step_uuid }
    }

    pub fn uuid(&self) -> u32 {
        self.step_uuid
    }

    pub fn next<F>(&self) -> Queriable<F> {
        Queriable::StepTypeNext(self.clone())
    }
}

pub struct ForwardSignalHandler {
    // fs: ForwardSignal,
}

pub fn circuit<F, TraceArgs, StepArgs, D>(name: &str, def: D) -> Circuit<F, TraceArgs, StepArgs>
where
    D: Fn(&mut CircuitContext<F, TraceArgs, StepArgs>),
{
    let mut context = CircuitContext {
        sc: Circuit::default(),
    };

    def(&mut context);

    context.sc
}

pub fn lookup_table<F, Args, D>(name: &str, def: D) -> LookupTable<F>
where
    D: Fn(&LookupWitnessGenContext<F>),
{
    todo!()
}
