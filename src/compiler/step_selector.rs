use std::{collections::HashMap, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::ast::{Circuit, StepType};

use super::{Column, PolyExpr};

pub type SelectorAssignment<F> = (PolyExpr<F>, F);

#[derive(Debug, Clone)]
pub struct StepSelector<F, Args> {
    pub selector_expr: HashMap<Rc<StepType<F, Args>>, PolyExpr<F>>,
    pub selector_expr_not: HashMap<Rc<StepType<F, Args>>, PolyExpr<F>>,
    pub selector_assignment: HashMap<Rc<StepType<F, Args>>, Vec<SelectorAssignment<F>>>,
    pub columns: Vec<Column>,
}

impl<F: Clone, Args> StepSelector<F, Args> {
    pub fn select(&self, step: &StepType<F, Args>, constraint: &PolyExpr<F>) -> PolyExpr<F> {
        let selector = self.selector_expr.get(step).expect("step not found");
        PolyExpr::Mul(vec![selector.clone(), constraint.clone()])
    }

    pub fn next_expr(&self, step: &StepType<F, Args>, step_height: u32) -> PolyExpr<F> {
        let selector = self.selector_expr.get(step).expect("step not found");

        selector.rotate(step_height as i32)
    }

    pub fn unselect(&self, step: &StepType<F, Args>) -> PolyExpr<F> {
        self.selector_expr_not
            .get(step)
            .expect("step not found {}")
            .clone()
    }
}

pub trait StepSelectorBuilder {
    fn build<F: Field, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> StepSelector<F, StepArgs>;
}

pub struct SimpleStepSelectorBuilder {}

impl StepSelectorBuilder for SimpleStepSelectorBuilder {
    fn build<F: Field, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> StepSelector<F, StepArgs> {
        let mut selector = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        for step in sc.step_types.values() {
            let annotation = if let Some(annotation) = sc.annotations.get(&step.uuid()) {
                format!("'step selector for {}'", annotation)
            } else {
                "'step selector'".to_string()
            };

            let column = Column::advice(annotation.clone(), 0);

            selector.columns.push(column.clone());

            selector.selector_expr.insert(
                Rc::clone(step),
                PolyExpr::Query(column.clone(), 0, annotation.clone()),
            );

            selector.selector_expr_not.insert(
                Rc::clone(step),
                PolyExpr::Sum(vec![
                    PolyExpr::Const(F::one()),
                    PolyExpr::Neg(Box::new(PolyExpr::Query(
                        column.clone(),
                        0,
                        annotation.clone(),
                    ))),
                ]),
            );

            selector.selector_assignment.insert(
                Rc::clone(step),
                vec![(PolyExpr::Query(column, 0, annotation), F::one())],
            );
        }

        selector
    }
}
