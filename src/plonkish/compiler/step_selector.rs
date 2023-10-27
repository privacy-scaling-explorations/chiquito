use std::{collections::HashMap, rc::Rc};

use halo2_proofs::plonk::{Advice, Column as Halo2Column};

use crate::{
    ast::{StepType, StepTypeUUID},
    field::Field,
    util::UUID,
};

use super::{Column, CompilationUnit, PolyExpr};

pub type SelectorAssignment<F> = (PolyExpr<F>, F);

#[derive(Debug, Clone)]
pub struct StepSelector<F> {
    pub selector_expr: HashMap<StepTypeUUID, PolyExpr<F>>,
    pub selector_expr_not: HashMap<StepTypeUUID, PolyExpr<F>>,
    pub selector_assignment: HashMap<StepTypeUUID, Option<Vec<SelectorAssignment<F>>>>,
    pub columns: Vec<Column>,
}

impl<F> Default for StepSelector<F> {
    fn default() -> Self {
        Self {
            selector_expr: Default::default(),
            selector_expr_not: Default::default(),
            selector_assignment: Default::default(),
            columns: Default::default(),
        }
    }
}

impl<F: Clone> StepSelector<F> {
    pub fn select(&self, step_uuid: StepTypeUUID, constraint: &PolyExpr<F>) -> PolyExpr<F> {
        let selector = self.selector_expr.get(&step_uuid).expect("step not found");
        PolyExpr::Mul(vec![selector.clone(), constraint.clone()])
    }

    pub fn next_expr(&self, step_uuid: StepTypeUUID, step_height: u32) -> PolyExpr<F> {
        let selector = self.selector_expr.get(&step_uuid).expect("step not found");

        selector.rotate(step_height as i32)
    }

    pub fn unselect(&self, step_uuid: StepTypeUUID) -> PolyExpr<F> {
        self.selector_expr_not
            .get(&step_uuid)
            .expect("step not found {}")
            .clone()
    }

    pub fn get_selector_assignment(
        &self,
        step_uuid: StepTypeUUID,
    ) -> Option<Vec<SelectorAssignment<F>>> {
        self.selector_assignment
            .get(&step_uuid)
            .expect("selector assignment for step not found")
            .clone()
    }
}

pub trait StepSelectorBuilder: Clone {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>);
}

#[derive(Debug, Default, Clone)]
pub struct SimpleStepSelectorBuilder {}

impl StepSelectorBuilder for SimpleStepSelectorBuilder {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>) {
        let mut selector = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        // don't add a column for a single step type
        if unit.step_types.len() == 1 {
            let step = unit.step_types.values().next().expect("step not found");

            // use F::ONE for selector constantly on, F::ZERO for off
            selector
                .selector_expr
                .insert(step.uuid(), PolyExpr::Const(F::ONE));

            selector
                .selector_expr_not
                .insert(step.uuid(), PolyExpr::Const(F::ZERO));

            selector.selector_assignment.insert(step.uuid(), None);

            unit.selector = selector;
            return;
        }

        for step in unit.step_types.values() {
            let annotation = if let Some(annotation) = unit.annotations.get(&step.uuid()) {
                format!("'step selector for {}'", annotation)
            } else {
                "'step selector'".to_string()
            };

            let column = Column::advice(annotation.clone(), 0);

            selector.columns.push(column.clone());

            selector
                .selector_expr
                .insert(step.uuid(), column.query(0, annotation.clone()));

            selector.selector_expr_not.insert(
                step.uuid(),
                PolyExpr::Const(F::ONE) + (-column.query(0, annotation.clone())),
            );

            selector.selector_assignment.insert(
                step.uuid(),
                Some(vec![(column.query(0, annotation.clone()), F::ONE)]),
            );
        }

        unit.columns.extend_from_slice(&selector.columns);
        unit.selector = selector;
    }
}

#[derive(Debug, Default, Clone)]
pub struct TwoStepsSelectorBuilder {
    pub halo2_column: Option<Halo2Column<Advice>>,
    pub hint_one: Option<String>,
}

impl StepSelectorBuilder for TwoStepsSelectorBuilder {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>) {
        if unit.step_types.len() != 2 {
            panic!("jarll: must have two step types");
        }

        unit.selector = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        let (step_zero, step_one) = if let Some(step_one_name) = self.hint_one.clone() {
            let hint_one = unit
                .step_types
                .values()
                .find(|&step_type| *step_type.name == step_one_name)
                .expect("step not found");

            let one_uuid = hint_one.uuid();
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

        let column = match self.halo2_column {
            Some(advice) => unit
                .find_halo2_advice_native(advice)
                .expect("column not found"),
            None => {
                let column = Column::advice("step selector for two steps", 0);
                unit.selector.columns.push(column.clone());
                unit.columns.push(column.clone());
                column
            }
        };

        // Zero
        unit.selector.selector_expr.insert(
            step_zero.uuid(),
            PolyExpr::Const(F::ONE) + (-column.query(0, "selector step zero")),
        );

        unit.selector
            .selector_expr_not
            .insert(step_zero.uuid(), column.query(0, "selector NOT step zero"));

        unit.selector.selector_assignment.insert(
            step_zero.uuid(),
            Some(vec![(column.query(0, "selector step zero"), F::ZERO)]),
        );

        // One
        unit.selector
            .selector_expr
            .insert(step_one.uuid(), column.query(0, "selector step one"));

        unit.selector.selector_expr_not.insert(
            step_one.uuid(),
            PolyExpr::Const(F::ONE) + (-column.query(0, "selector NOT step one")),
        );

        unit.selector.selector_assignment.insert(
            step_one.uuid(),
            Some(vec![(column.query(0, "selector step one"), F::ONE)]),
        );
    }
}

fn other_step_type<F>(unit: &CompilationUnit<F>, uuid: UUID) -> Option<Rc<StepType<F>>> {
    for step_type in unit.step_types.values() {
        if step_type.uuid() != uuid {
            return Some(Rc::clone(step_type));
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::Constraint,
        frontend::dsl::cb::eq,
        plonkish::compiler::{transform_expr, CompilationUnit},
        poly::ToExpr,
    };
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_ssb_single_step() {
        // unit test for SSB with only one step type
        let mut unit = CompilationUnit::<Fr>::default();
        let step = StepType::<Fr>::new(UUID::default(), "single step".to_string());
        let uuid = step.uuid();
        unit.annotations.insert(uuid, step.name.clone());
        unit.step_types.insert(uuid, Rc::new(step));

        let ssb = SimpleStepSelectorBuilder {};
        ssb.build(&mut unit);

        let constraint = Constraint::<Fr> {
            annotation: "test constraint".to_string(),
            expr: eq(1.expr() - 1.expr(), 0.expr()).into(),
        };
        let constraint = transform_expr(
            &unit,
            unit.step_types.get(&uuid).expect("step not found {}"),
            &constraint.expr,
        );

        // selector.select should return constraint switched on
        assert_eq!(
            format!("{:?}", unit.selector.select(uuid, &constraint)),
            format!(
                "{:?}",
                PolyExpr::Mul(vec![PolyExpr::Const(Fr::ONE), constraint])
            )
        );
        assert_eq!(
            format!("{:?}", unit.selector.unselect(uuid)),
            format!("{:?}", PolyExpr::Const(Fr::ZERO))
        );
        assert_eq!(
            format!("{:?}", unit.selector.next_expr(uuid, 1)),
            format!("{:?}", PolyExpr::Const(Fr::ONE))
        );
        assert!(unit.selector.get_selector_assignment(uuid).is_none());
    }
}
