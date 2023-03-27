use std::{collections::HashMap, rc::Rc};

use crate::ast::{Circuit, StepType};

use super::{Column, PolyExpr};

pub struct StepSelector<F, Args> {
    pub selector_expr: HashMap<Rc<StepType<F, Args>>, PolyExpr<F>>,
    pub columns: Vec<Column>,
}

impl<F: Clone, Args> StepSelector<F, Args> {
    pub fn select(&self, step: &StepType<F, Args>, constraint: &PolyExpr<F>) -> PolyExpr<F> {
        let selector = self.selector_expr.get(step).expect("step not found");
        PolyExpr::Mul(vec![selector.clone(), constraint.clone()])
    }
}

pub trait StepSelectorBuilder {
    fn build<F, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> StepSelector<F, StepArgs>;
}

pub struct SimpleStepSelectorBuilder {}

impl StepSelectorBuilder for SimpleStepSelectorBuilder {
    fn build<F, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> StepSelector<F, StepArgs> {
        let mut selector = StepSelector {
            selector_expr: HashMap::new(),
            columns: Vec::new(),
        };

        for step in sc.step_types.values().into_iter() {
            let column = Column::new("step selector");

            selector.columns.push(column.clone());

            selector.selector_expr.insert(
                Rc::clone(&step),
                PolyExpr::Query(column, 0, "selector".to_string()),
            );
        }

        selector
    }
}
