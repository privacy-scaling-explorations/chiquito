use std::{collections::HashMap, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::{query::Queriable, StepType},
    dsl::StepTypeHandler,
};

use super::{Column, CompilationUnit, PolyExpr};

pub type SelectorAssignment<F> = (PolyExpr<F>, F);

#[derive(Debug, Clone)]
pub struct StepSelector<F, Args> {
    pub selector_expr: HashMap<Rc<StepType<F, Args>>, PolyExpr<F>>,
    pub selector_expr_not: HashMap<Rc<StepType<F, Args>>, PolyExpr<F>>,
    pub selector_assignment: HashMap<Rc<StepType<F, Args>>, Vec<SelectorAssignment<F>>>,
    pub columns: Vec<Column>,
}

impl<F, Args> Default for StepSelector<F, Args> {
    fn default() -> Self {
        Self {
            selector_expr: Default::default(),
            selector_expr_not: Default::default(),
            selector_assignment: Default::default(),
            columns: Default::default(),
        }
    }
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
    fn build<F: Field, TraceArgs, StepArgs>(&self, unit: &mut CompilationUnit<F, StepArgs>);
}

pub struct SimpleStepSelectorBuilder {}

impl StepSelectorBuilder for SimpleStepSelectorBuilder {
    fn build<F: Field, TraceArgs, StepArgs>(&self, unit: &mut CompilationUnit<F, StepArgs>) {
        let mut selector = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        for step in unit.step_types.values() {
            let annotation = if let Some(annotation) = unit.annotations.get(&step.uuid()) {
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

        unit.columns.extend_from_slice(&selector.columns);
        unit.selector = selector;
    }
}

pub struct TwoStepsSelectorBuilder<F> {
    pub signal: Option<Queriable<F>>,
    pub hint_one: Option<StepTypeHandler>,
}

impl<F: Field> StepSelectorBuilder for TwoStepsSelectorBuilder<F> {
    fn build<F2: Field, TraceArgs, StepArgs>(&self, unit: &mut CompilationUnit<F2, StepArgs>) {
        if unit.step_types.len() != 2 {
            panic!("jarll: must have two step types");
        }

        unit.selector = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        let (step_zero, step_one) = if let Some(one) = self.hint_one {
            let one_uuid = one.uuid();
            let step_one = unit.step_types.get(&one_uuid).expect("step not found");
            let step_zero = other_step_type(unit, one_uuid).expect("step not found");
            (step_zero, step_one.clone())
        } else {
            let mut iter = unit.step_types.values();

            (
                Rc::clone(iter.next().expect("step not found")),
                Rc::clone(iter.next().expect("step not found")),
            )
        };

        let column = match self.signal {
            Some(Queriable::Halo2AdviceQuery(advice, rot)) => {
                if rot != 0 {
                    panic!("jarll: signal should have 0 rotation");
                }
                unit.find_halo2_advice(advice).expect("column not found")
            }
            None => {
                let column = Column::advice("step selector for two steps", 0);
                unit.selector.columns.push(column.clone());
                unit.columns.push(column.clone());
                column
            }
            _ => panic!("jarll: wrong signal type"),
        };

        // Zero
        unit.selector.selector_expr.insert(
            Rc::clone(&step_zero),
            PolyExpr::Sum(vec![
                PolyExpr::Const(F2::one()),
                PolyExpr::Neg(Box::new(PolyExpr::Query(
                    column.clone(),
                    0,
                    "selector step zero".to_string(),
                ))),
            ]),
        );

        unit.selector.selector_expr_not.insert(
            Rc::clone(&step_zero),
            PolyExpr::Query(column.clone(), 0, "selector NOT step zero".to_string()),
        );

        unit.selector.selector_assignment.insert(
            Rc::clone(&step_zero),
            vec![(
                PolyExpr::Query(column.clone(), 0, "select step zero".to_string()),
                F2::zero(),
            )],
        );

        // One
        unit.selector.selector_expr.insert(
            Rc::clone(&step_one),
            PolyExpr::Query(column.clone(), 0, "selector step one".to_string()),
        );

        unit.selector.selector_expr_not.insert(
            Rc::clone(&step_one),
            PolyExpr::Sum(vec![
                PolyExpr::Const(F2::one()),
                PolyExpr::Neg(Box::new(PolyExpr::Query(
                    column.clone(),
                    0,
                    "selector NOT step one".to_string(),
                ))),
            ]),
        );

        unit.selector.selector_assignment.insert(
            Rc::clone(&step_one),
            vec![(
                PolyExpr::Query(column, 0, "select step one".to_string()),
                F2::one(),
            )],
        );
    }
}

fn other_step_type<F, StepArgs>(
    unit: &CompilationUnit<F, StepArgs>,
    uuid: u32,
) -> Option<Rc<StepType<F, StepArgs>>> {
    for step_type in unit.step_types.values() {
        if step_type.uuid() != uuid {
            return Some(Rc::clone(step_type));
        }
    }

    None
}
