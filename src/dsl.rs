use crate::{
    ast::{Expr, Queriable, StepType, SuperCircuit},
    compiler::{TraceContext, WitnessGenContext},
};

pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: SuperCircuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
    pub fn forward(&mut self, name: &str) -> Queriable {
        Queriable::Forward(self.sc.add_forward(name))
    }

    pub fn step_type<D>(&mut self, name: &str, def: D) -> StepTypeHandler
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context = StepTypeContext::<F, StepArgs>::default();

        def(&mut context);

        self.sc.add_step_type(context.step_type);

        // TODO meaningful StepTypeHandler
        StepTypeHandler {}
    }

    pub fn trace<D>(&mut self, def: D)
    where
        D: FnOnce(&TraceContext<StepArgs>, TraceArgs) + 'static,
    {
        self.sc.set_trace(def);
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
    pub fn signal(&mut self, name: &str) -> Queriable {
        Queriable::Internal(self.step_type.add_signal(name))
    }

    pub fn cond(&mut self, annotation: &str, expr: Expr<F>) {
        self.step_type.add_cond(annotation, expr);
    }

    pub fn transition<D: Into<Expr<F>>>(&mut self, annotation: &str, expr: D) {
        self.step_type.add_transition(annotation, expr.into());
    }

    pub fn wg<D>(&mut self, def: D)
    where
        D: FnOnce(&WitnessGenContext<F>, Args) + 'static,
    {
        self.step_type.set_wg(def);
    }
}

pub struct StepTypeHandler {
    // s: Step,
}

pub struct ForwardSignalHandler {
    // fs: ForwardSignal,
}

pub struct CircuitDefinition<F, TraceArgs, StepArgs> {
    sc: SuperCircuit<F, TraceArgs, StepArgs>,
}

pub fn circuit<F, TraceArgs, StepArgs, D>(
    name: &str,
    def: D,
) -> CircuitDefinition<F, TraceArgs, StepArgs>
where
    D: Fn(&mut CircuitContext<F, TraceArgs, StepArgs>),
{
    let mut context = CircuitContext {
        sc: SuperCircuit::default(),
    };

    def(&mut context);

    CircuitDefinition { sc: context.sc }
}
