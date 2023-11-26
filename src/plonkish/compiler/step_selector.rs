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
    pub selector_assignment: HashMap<StepTypeUUID, Vec<SelectorAssignment<F>>>,
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

    pub fn get_selector_assignment(&self, step_uuid: StepTypeUUID) -> Vec<SelectorAssignment<F>> {
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
                vec![(column.query(0, annotation.clone()), F::ONE)],
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
            vec![(column.query(0, "selector step zero"), F::ZERO)],
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
            vec![(column.query(0, "selector step one"), F::ONE)],
        );
    }
}

#[derive(Debug, Default, Clone)]
pub struct LogNSelectorBuilder {}

impl StepSelectorBuilder for LogNSelectorBuilder {
    fn build<F: Field>(&self, unit: &mut CompilationUnit<F>) {
        let mut selector: StepSelector<F> = StepSelector {
            selector_expr: HashMap::new(),
            selector_expr_not: HashMap::new(),
            selector_assignment: HashMap::new(),
            columns: Vec::new(),
        };

        let n_step_types = unit.step_types.len() as u64;
        let n_cols = (n_step_types as f64 + 1.0).log2().ceil() as u64;

        let mut annotation;
        for index in 0..n_cols {
            annotation = format!("'binary selector column {}'", index);

            let column = Column::advice(annotation.clone(), 0);
            selector.columns.push(column.clone());
        }

        let mut step_value = 1;
        for step in unit.step_types.values() {
            let mut combined_expr = PolyExpr::Const(F::ONE);
            let mut assignments = Vec::new();

            for i in 0..n_cols {
                let bit = (step_value >> i) & 1; // Extract the i-th bit of step_value
                let column = &selector.columns[i as usize];

                if bit == 1 {
                    combined_expr = combined_expr * column.query(0, format!("Column {}", i));
                    assignments.push((column.query(0, format!("Column {}", i)), F::ONE));
                } else {
                    combined_expr = combined_expr
                        * (PolyExpr::Const(F::ONE) - column.query(0, format!("Column {}", i)));
                }
            }

            selector
                .selector_expr
                .insert(step.uuid(), combined_expr.clone());
            selector
                .selector_expr_not
                .insert(step.uuid(), PolyExpr::Const(F::ONE) - combined_expr.clone());
            selector
                .selector_assignment
                .insert(step.uuid(), assignments);
            step_value += 1;
        }

        unit.columns.extend_from_slice(&selector.columns);
        unit.selector = selector;
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
    use halo2curves::bn256::Fr;
    use uuid::Uuid;

    use super::*;

    fn mock_compilation_unit<F>() -> CompilationUnit<F> {
        CompilationUnit::default()
    }

    fn add_step_types_to_unit<F>(unit: &mut CompilationUnit<F>, n_step_types: usize) {
        for i in 0..n_step_types {
            let uuid_value = Uuid::now_v1(&[1, 2, 3, 4, 5, 6]).as_u128();
            unit.step_types.insert(
                uuid_value,
                Rc::new(StepType::new(uuid_value, format!("StepType{}", i))),
            );
        }
    }

    fn assert_common_tests<F>(unit: &CompilationUnit<F>, expected_cols: usize) {
        assert_eq!(unit.columns.len(), expected_cols);
        assert_eq!(unit.selector.columns.len(), expected_cols);
        for step_type in unit.step_types.values() {
            assert!(unit
                .selector
                .selector_assignment
                .contains_key(&step_type.uuid()));
            assert!(unit.selector.selector_expr.contains_key(&step_type.uuid()));
        }
    }

    #[test]
    fn test_log_n_selector_builder_3_step_types() {
        let builder = LogNSelectorBuilder {};
        let mut unit = mock_compilation_unit::<Fr>();

        add_step_types_to_unit(&mut unit, 3);
        builder.build(&mut unit);
        assert_common_tests(&unit, 2);

        // Asserts expressions for 3 step types
        let expr10_temp = format!(
            "(0x1 * {:#?} * (0x1 + (-{:#?})))",
            &unit.selector.columns[0].query::<i32, &str>(0, "Column 0"),
            &unit.selector.columns[1].query::<i32, &str>(0, "Column 1")
        );
        let expr01_temp = format!(
            "(0x1 * (0x1 + (-{:#?})) * {:#?})",
            &unit.selector.columns[0].query::<i32, &str>(0, "Column 0"),
            &unit.selector.columns[1].query::<i32, &str>(0, "Column 1")
        );
        let expr11_temp = format!(
            "(0x1 * {:#?} * {:#?})",
            &unit.selector.columns[0].query::<i32, &str>(0, "Column 0"),
            &unit.selector.columns[1].query::<i32, &str>(0, "Column 1")
        );
        let expected_exprs = [expr01_temp.trim(), expr10_temp.trim(), expr11_temp.trim()];

        for expr in unit.selector.selector_expr.values() {
            let expr_str = format!("{:#?}", expr);
            assert!(
                expected_exprs.contains(&expr_str.trim()),
                "Unexpected expression: {}",
                expr_str
            );
        }
    }

    #[test]
    fn test_log_n_selector_builder_4_step_types() {
        let builder = LogNSelectorBuilder {};
        let mut unit = mock_compilation_unit::<Fr>();

        add_step_types_to_unit(&mut unit, 4);
        builder.build(&mut unit);
        assert_common_tests(&unit, 3);
    }

    #[test]
    fn test_log_n_selector_builder_10_step_types() {
        let builder = LogNSelectorBuilder {};
        let mut unit = mock_compilation_unit::<Fr>();

        add_step_types_to_unit(&mut unit, 10);
        builder.build(&mut unit);

        let expected_cols = (10_f64 + 1.0).log2().ceil() as usize;
        assert_common_tests(&unit, expected_cols);
    }
}
