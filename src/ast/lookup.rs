use crate::compiler::LookupWitnessGenContext;

use super::{Constraint, Expr, ForwardSignal};

pub type LookupTableWG<F, Args> = dyn FnOnce(&LookupWitnessGenContext<F>, Args);

pub struct LookupTable<F, Args> {
    pub forward_signals: Vec<ForwardSignal>,
    pub constraints: Vec<Constraint<F>>,
    pub wg: Option<Box<LookupTableWG<F, Args>>>,
}

impl<F, Args> LookupTable<F, Args> {
    pub fn add_signal(&mut self, name: &str) -> ForwardSignal {
        let signal = ForwardSignal::new();

        self.forward_signals.push(signal);

        signal
    }

    pub fn add_constr(&mut self, annotation: &str, expr: Expr<F>) {
        let condition = Constraint {
            annotation: annotation.to_string(),
            expr,
        };

        self.constraints.push(condition)
    }

    pub fn wg<D: Fn(&LookupWitnessGenContext<F>, Args)>(&mut self, def: D) {
        self.wg = Some(def)
    }
}
