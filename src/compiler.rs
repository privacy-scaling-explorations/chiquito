use core::fmt::Debug;
use std::{collections::HashMap, hash::Hash, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    plonk::{Advice, Column as Halo2Column},
};

use crate::{
    ast::{
        query::Queriable, Circuit as astCircuit, ExposeOffset, Expr, FixedSignal, ForwardSignal,
        ImportedHalo2Advice, ImportedHalo2Fixed, SharedSignal, StepType, StepTypeUUID,
    },
    ir::{
        assigments::{AssigmentGenerator, Assignments},
        Circuit, Column, ColumnType, Poly, PolyExpr, PolyLookup,
    },
    util::{uuid, UUID},
    wit_gen::{FixedAssignment, FixedGenContext, TraceGenerator},
};

use self::{
    cell_manager::{CellManager, Placement, SignalPlacement},
    step_selector::{StepSelector, StepSelectorBuilder},
};

pub mod cell_manager;
pub mod step_selector;

#[derive(Debug, Clone)]
pub struct CompilationUnit<F> {
    pub placement: Placement,
    pub selector: StepSelector<F>,
    pub step_types: HashMap<UUID, Rc<StepType<F>>>,
    pub forward_signals: Vec<ForwardSignal>,
    pub shared_signals: Vec<SharedSignal>,
    pub fixed_signals: Vec<FixedSignal>,

    pub annotations: HashMap<UUID, String>,

    pub columns: Vec<Column>,
    pub exposed: Vec<(Column, i32)>,

    pub num_steps: usize,
    pub q_enable: Option<Column>,
    pub first_step: Option<(StepTypeUUID, Column)>,
    pub last_step: Option<(Option<StepTypeUUID>, Column)>,

    pub num_rows: usize,

    pub polys: Vec<Poly<F>>,
    pub lookups: Vec<PolyLookup<F>>,

    pub fixed_assignments: Assignments<F>,

    pub ast_id: UUID,
    pub uuid: UUID,

    pub other_sub_circuits: Rc<Vec<CompilationUnit<F>>>,
    pub other_columns: Rc<Vec<Column>>,
}

impl<F> Default for CompilationUnit<F> {
    fn default() -> Self {
        Self {
            placement: Default::default(),
            selector: Default::default(),
            step_types: Default::default(),
            forward_signals: Default::default(),
            shared_signals: Default::default(),
            fixed_signals: Default::default(),

            annotations: Default::default(),

            columns: Default::default(),
            exposed: Default::default(),

            num_steps: Default::default(),
            q_enable: Default::default(),
            first_step: Default::default(),
            last_step: Default::default(),

            num_rows: Default::default(),

            polys: Default::default(),
            lookups: Default::default(),

            fixed_assignments: Default::default(),

            ast_id: Default::default(),
            uuid: uuid(),

            other_sub_circuits: Default::default(),
            other_columns: Default::default(),
        }
    }
}

impl<F> CompilationUnit<F> {
    fn find_halo2_advice(&self, to_find: ImportedHalo2Advice) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_advice(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    fn find_halo2_advice_native(&self, to_find: Halo2Column<Advice>) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice.column == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_advice_native(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    fn find_halo2_fixed(&self, to_find: ImportedHalo2Fixed) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(fixed) = column.halo2_fixed {
                if fixed == to_find {
                    return Some(column.clone());
                }
            }
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            let found = sub_circuit.find_halo2_fixed(to_find);
            if found.is_some() {
                return found;
            }
        }

        None
    }

    pub fn get_forward_placement(&self, forward: &ForwardSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_forward_placement(forward) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(placement) = sub_circuit.placement.get_forward_placement(forward) {
                return placement;
            }
        }

        panic!("forward signal placement not found");
    }
    pub fn get_shared_placement(&self, shared: &SharedSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_shared_placement(shared) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(placement) = sub_circuit.placement.get_shared_placement(shared) {
                return placement;
            }
        }

        panic!("shared signal placement not found");
    }

    pub fn get_fixed_placement(&self, fixed: &FixedSignal) -> SignalPlacement {
        if let Some(placement) = self.placement.get_fixed_placement(fixed) {
            return placement;
        }

        for sub_circuit in self.other_sub_circuits.iter() {
            if let Some(signal) = sub_circuit.placement.get_fixed_placement(fixed) {
                return signal;
            }
        }

        panic!("fixed signal placement not found");
    }

    fn has_transition_constraints<TraceArgs>(ast: &astCircuit<F, TraceArgs>) -> bool {
        for step in ast.step_types.values() {
            if !step.transition_constraints.is_empty() {
                return true;
            }
        }

        false
    }
}

impl<F, TraceArgs> From<&astCircuit<F, TraceArgs>> for CompilationUnit<F> {
    fn from(ast: &astCircuit<F, TraceArgs>) -> Self {
        CompilationUnit::<F> {
            annotations: {
                let mut acc = ast.annotations.clone();
                for step in ast.step_types.values() {
                    acc.extend(step.annotations.clone());
                }

                acc
            },
            step_types: ast.step_types.clone(),
            forward_signals: ast.forward_signals.clone(),
            shared_signals: ast.shared_signals.clone(),
            fixed_signals: ast.fixed_signals.clone(),
            num_steps: ast.num_steps,
            q_enable: if ast.q_enable {
                Some(Column {
                    annotation: "q_enable".to_owned(),
                    ctype: ColumnType::Fixed,
                    halo2_advice: None,
                    halo2_fixed: None,
                    phase: 0,
                    id: uuid(),
                })
            } else {
                None
            },
            first_step: ast.first_step.map(|step_type_uuid| {
                (
                    step_type_uuid,
                    Column {
                        annotation: "q_first".to_owned(),
                        ctype: ColumnType::Fixed,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: uuid(),
                    },
                )
            }),
            last_step: if ast.last_step.is_some() || Self::has_transition_constraints(ast) {
                Some((
                    ast.last_step,
                    Column {
                        annotation: "q_last".to_owned(),
                        ctype: ColumnType::Fixed,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: uuid(),
                    },
                ))
            } else {
                None
            },
            ast_id: ast.id,
            ..Default::default()
        }
    }
}

impl<F> From<CompilationUnit<F>> for Circuit<F> {
    fn from(unit: CompilationUnit<F>) -> Self {
        Circuit::<F> {
            columns: unit.columns,
            exposed: unit.exposed,
            polys: unit.polys,
            lookups: unit.lookups,
            fixed_assignments: unit.fixed_assignments,
            id: unit.uuid,
            ast_id: unit.ast_id,
        }
    }
}

#[derive(Clone)]
pub struct CompilerConfig<CM: CellManager, SSB: StepSelectorBuilder> {
    cell_manager: CM,
    step_selector_builder: SSB,
}

pub fn config<CM: CellManager, SSB: StepSelectorBuilder>(
    cell_manager: CM,
    step_selector_builder: SSB,
) -> CompilerConfig<CM, SSB> {
    CompilerConfig {
        cell_manager,
        step_selector_builder,
    }
}

pub struct Compiler<CM: CellManager, SSB: StepSelectorBuilder> {
    cell_manager: CM,
    step_selector_builder: SSB,
}

impl<CM: CellManager, SSB: StepSelectorBuilder> From<CompilerConfig<CM, SSB>>
    for Compiler<CM, SSB>
{
    fn from(config: CompilerConfig<CM, SSB>) -> Self {
        Compiler::new(config.cell_manager, config.step_selector_builder)
    }
}

impl<CM: CellManager, SSB: StepSelectorBuilder> Compiler<CM, SSB> {
    pub fn new(cell_manager: CM, step_selector_builder: SSB) -> Compiler<CM, SSB> {
        Compiler {
            cell_manager,
            step_selector_builder,
        }
    }

    pub fn compile<F: Field + Hash + Clone, TraceArgs>(
        &self,
        ast: &astCircuit<F, TraceArgs>,
    ) -> (Circuit<F>, Option<AssigmentGenerator<F, TraceArgs>>) {
        let (mut unit, assignment) = self.compile_phase1(ast);

        self.compile_phase2(&mut unit);

        (unit.into(), assignment)
    }

    pub fn compile_phase1<F: Field + Hash + Clone, TraceArgs>(
        &self,
        ast: &astCircuit<F, TraceArgs>,
    ) -> (CompilationUnit<F>, Option<AssigmentGenerator<F, TraceArgs>>) {
        let mut unit = CompilationUnit::from(ast);

        self.add_halo2_columns(&mut unit, ast);

        self.cell_manager.place(&mut unit);

        if (!unit.shared_signals.is_empty() || !unit.fixed_signals.is_empty())
            && !unit.placement.same_height()
        {
            panic!("Shared signals and fixed signals are not supported for circuits with different step heights. Using a different cell manager might fix this problem.");
        }

        if !unit.placement.same_height() {
            panic!("Cannot calculate the number of rows");
        }
        unit.num_rows = unit.num_steps * (unit.placement.first_step_height() as usize);

        self.compile_fixed(ast, &mut unit);

        self.compile_exposed(ast, &mut unit);

        self.add_default_columns(&mut unit);

        self.step_selector_builder.build::<F>(&mut unit);

        let assigment = ast.trace.as_ref().map(|v| {
            AssigmentGenerator::new(
                unit.columns.clone(),
                unit.placement.clone(),
                unit.selector.clone(),
                TraceGenerator::new(Rc::clone(v)),
                unit.num_rows,
                unit.uuid,
            )
        });

        (unit, assigment)
    }

    pub fn compile_phase2<F: Field + Clone>(&self, unit: &mut CompilationUnit<F>) {
        for step in unit.step_types.clone().values() {
            self.compile_step(unit, step);
        }

        if let Some(q_enable) = &unit.q_enable {
            self.add_q_enable(unit, q_enable.clone());
        }

        if let Some((step_type, q_first)) = &unit.first_step {
            self.add_q_first(unit, *step_type, q_first.clone());
        }

        if let Some((step_type, q_last)) = &unit.last_step {
            self.add_q_last(unit, *step_type, q_last.clone());
        }
    }

    fn compile_step<F: Field>(&self, unit: &mut CompilationUnit<F>, step: &StepType<F>) {
        let step_annotation = unit
            .annotations
            .get(&step.uuid())
            .unwrap_or(&"??".to_string())
            .to_owned();

        for constr in step.constraints.iter() {
            let constraint = self.transform_expr(unit, step, &constr.expr.clone());
            let poly = unit.selector.select(step.uuid(), &constraint);

            unit.polys.push(Poly {
                expr: poly,
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        // TODO only transition_constraints should have rotations
        for constr in step.transition_constraints.iter() {
            let constraint = self.transform_expr(unit, step, &constr.expr.clone());
            let poly = unit.selector.select(step.uuid(), &constraint);
            let poly = Self::add_q_last_to_constraint(unit, poly);

            unit.polys.push(Poly {
                expr: poly,
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        for lookup in step.lookups.iter() {
            let poly_lookup = PolyLookup {
                annotation: lookup.annotation.clone(),
                exprs: lookup
                    .exprs
                    .iter()
                    .map(|(src, dest)| {
                        let src_poly = self.transform_expr(unit, step, &src.expr);
                        let dest_poly = self.transform_expr(unit, step, dest);
                        let src_selected = unit.selector.select(step.uuid(), &src_poly);

                        (src_selected, dest_poly)
                    })
                    .collect(),
            };

            unit.lookups.push(poly_lookup);
        }
    }

    fn compile_exposed<F, TraceArgs>(
        &self,
        ast: &astCircuit<F, TraceArgs>,
        unit: &mut CompilationUnit<F>,
    ) {
        for (queriable, offset) in &ast.exposed {
            let exposed = match queriable {
                Queriable::Forward(forward_signal, _) => {
                    let placement = unit
                        .placement
                        .get_forward_placement(forward_signal)
                        .expect("forward placement not found");
                    match offset {
                        ExposeOffset::First => (placement.column, placement.rotation),
                        ExposeOffset::Last => {
                            let rot = placement.rotation
                                + ((unit.num_steps - 1) as i32)
                                    * (unit.placement.first_step_height() as i32);
                            (placement.column, rot)
                        }
                        ExposeOffset::Step(step) => {
                            let rot = placement.rotation
                                + (*step as i32) * (unit.placement.first_step_height() as i32);
                            (placement.column, rot)
                        }
                    }
                }
                Queriable::Shared(shared_signal, _) => {
                    let placement = unit
                        .placement
                        .get_shared_placement(shared_signal)
                        .expect("shared placement not found");
                    match offset {
                        ExposeOffset::First => (placement.column, placement.rotation),
                        ExposeOffset::Last => {
                            let rot = placement.rotation
                                + ((unit.num_steps - 1) as i32)
                                    * (unit.placement.first_step_height() as i32);
                            (placement.column, rot)
                        }
                        ExposeOffset::Step(step) => {
                            let rot = placement.rotation
                                + (*step as i32) * (unit.placement.first_step_height() as i32);
                            (placement.column, rot)
                        }
                    }
                }
                _ => panic!("Queriable was not Forward or Shared"),
            };

            unit.exposed.push(exposed);
        }
    }

    fn compile_fixed<F: Field + Hash, TraceArgs>(
        &self,
        ast: &astCircuit<F, TraceArgs>,
        unit: &mut CompilationUnit<F>,
    ) {
        if let Some(fixed_gen) = &ast.fixed_gen {
            let mut ctx = FixedGenContext::new(unit.num_steps);
            (*fixed_gen)(&mut ctx);

            let assignments = ctx.get_assigments();

            unit.fixed_assignments = self.place_fixed_assignments(unit, assignments);
        }
    }

    fn place_queriable<F: Clone>(
        &self,
        unit: &CompilationUnit<F>,
        step: &StepType<F>,
        q: Queriable<F>,
    ) -> PolyExpr<F> {
        match q {
            Queriable::Internal(signal) => {
                let placement = unit
                    .placement
                    .find_internal_signal_placement(step.uuid(), &signal);

                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    format!(
                        "{}[{}, {}]",
                        annotation, placement.column.annotation, placement.rotation
                    )
                } else {
                    format!("[{}, {}]", placement.column.annotation, placement.rotation)
                };

                PolyExpr::Query(placement.column, placement.rotation, annotation)
            }
            Queriable::Forward(forward, next) => {
                let placement = unit.get_forward_placement(&forward);

                let super_rotation = placement.rotation
                    + if next {
                        unit.placement.step_height(step.uuid()) as i32
                    } else {
                        0
                    };

                let annotation = if let Some(annotation) = unit.annotations.get(&forward.uuid()) {
                    if next {
                        format!(
                            "next({})[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    } else {
                        format!(
                            "{}[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    }
                } else {
                    format!("[{}, {}]", placement.column.annotation, super_rotation)
                };
                PolyExpr::Query(placement.column, super_rotation, annotation)
            }
            Queriable::Shared(shared, rot) => {
                let placement = unit.get_shared_placement(&shared);

                let super_rotation =
                    placement.rotation + rot * (unit.placement.step_height(step.uuid()) as i32);

                let annotation = if let Some(annotation) = unit.annotations.get(&shared.uuid()) {
                    if rot == 0 {
                        format!(
                            "{}[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    } else {
                        format!(
                            "shared_rot_{}({})[{}, {}]",
                            rot, annotation, placement.column.annotation, super_rotation
                        )
                    }
                } else {
                    format!("[{}, {}]", placement.column.annotation, super_rotation)
                };
                PolyExpr::Query(placement.column, super_rotation, annotation)
            }
            Queriable::Fixed(fixed, rot) => {
                let placement = unit.get_fixed_placement(&fixed);

                let super_rotation =
                    placement.rotation + rot * (unit.placement.step_height(step.uuid()) as i32);

                let annotation = if let Some(annotation) = unit.annotations.get(&fixed.uuid()) {
                    if rot == 0 {
                        format!(
                            "{}[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    } else {
                        format!(
                            "fixed_rot_{}({})[{}, {}]",
                            rot, annotation, placement.column.annotation, super_rotation
                        )
                    }
                } else {
                    format!("[{}, {}]", placement.column.annotation, super_rotation)
                };
                PolyExpr::Query(placement.column, super_rotation, annotation)
            }
            Queriable::StepTypeNext(step_type_handle) => {
                let super_rotation = unit.placement.step_height(step.uuid());
                let dest_step = unit
                    .step_types
                    .get(&step_type_handle.uuid())
                    .expect("step not found");

                unit.selector.next_expr(dest_step.uuid(), super_rotation)
            }
            Queriable::Halo2AdviceQuery(signal, rot) => {
                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    format!("[{}, {}]", annotation, rot)
                } else {
                    format!("[halo2_advice?, {}]", rot)
                };
                PolyExpr::Query(
                    unit.find_halo2_advice(signal)
                        .expect("halo2 advice column not found"),
                    rot,
                    annotation,
                )
            }
            Queriable::Halo2FixedQuery(signal, rot) => {
                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    format!("[{}, {}]", annotation, rot)
                } else {
                    format!("[halo2_fixed?, {}]", rot)
                };
                PolyExpr::Query(
                    unit.find_halo2_fixed(signal)
                        .expect("halo2 fixed column not found"),
                    rot,
                    annotation,
                )
            }
            Queriable::_unaccessible(_) => panic!("jarrl"),
        }
    }

    fn transform_expr<F: Clone>(
        &self,
        unit: &CompilationUnit<F>,
        step: &StepType<F>,
        source: &Expr<F>,
    ) -> PolyExpr<F> {
        match source.clone() {
            Expr::Const(c) => PolyExpr::Const(c),
            Expr::Sum(v) => PolyExpr::Sum(
                v.into_iter()
                    .map(|e| self.transform_expr(unit, step, &e))
                    .collect(),
            ),
            Expr::Mul(v) => PolyExpr::Mul(
                v.into_iter()
                    .map(|e| self.transform_expr(unit, step, &e))
                    .collect(),
            ),
            Expr::Neg(v) => PolyExpr::Neg(Box::new(self.transform_expr(unit, step, &v))),
            Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(self.transform_expr(unit, step, &v)), exp),
            Expr::Query(q) => self.place_queriable(unit, step, q),
            Expr::Halo2Expr(expr) => PolyExpr::Halo2Expr(expr),
        }
    }

    fn place_fixed_assignments<F: Field>(
        &self,
        unit: &CompilationUnit<F>,
        assignments: FixedAssignment<F>,
    ) -> Assignments<F> {
        let mut result = Assignments::default();
        let step_height = unit.placement.first_step_height();
        let empty = vec![F::ZERO; unit.num_rows];

        for (queriable, assignments) in assignments {
            let placement = match queriable {
                Queriable::Fixed(fixed, rot) => {
                    if rot != 0 {
                        panic!("cannot do fixed assignation of rotated queriable");
                    }
                    unit.placement
                        .get_fixed_placement(&fixed)
                        .expect("fixed placement not found")
                }
                Queriable::Halo2FixedQuery(signal, rot) => SignalPlacement::new(
                    unit.find_halo2_fixed(signal).expect("column not found"),
                    rot,
                ),
                _ => panic!("only can do fixed assignment to fixed signal"),
            };

            let mut column_values = if let Some(column_values) = result.get(&placement.column) {
                column_values.clone()
            } else {
                empty.clone()
            };

            let mut offset = placement.rotation as usize;
            for value in assignments {
                column_values[offset] = value;
                offset += step_height as usize;
            }

            result.insert(placement.column, column_values);
        }

        result
    }

    fn add_q_enable<F: Field>(&self, unit: &mut CompilationUnit<F>, q_enable: Column) {
        unit.polys = unit
            .polys
            .iter()
            .map(|poly| Poly {
                annotation: poly.annotation.clone(),
                expr: PolyExpr::Mul(vec![
                    PolyExpr::<F>::Query(q_enable.clone(), 0, "q_enable".to_owned()),
                    poly.expr.clone(),
                ]),
            })
            .collect();

        unit.lookups = unit
            .lookups
            .iter()
            .map(|lookup| PolyLookup {
                annotation: lookup.annotation.clone(),
                exprs: lookup
                    .exprs
                    .iter()
                    .map(|(src, dest)| {
                        (
                            PolyExpr::Mul(vec![
                                PolyExpr::<F>::Query(q_enable.clone(), 0, "q_enable".to_owned()),
                                src.clone(),
                            ]),
                            dest.clone(),
                        )
                    })
                    .collect(),
            })
            .collect();

        let assignments = vec![F::ONE; unit.num_rows];
        unit.fixed_assignments.insert(q_enable, assignments);
    }

    fn add_q_first<F: Field>(
        &self,
        unit: &mut CompilationUnit<F>,
        step_uuid: StepTypeUUID,
        q_first: Column,
    ) {
        let step = unit.step_types.get(&step_uuid).expect("step not found");

        let poly = PolyExpr::Mul(vec![
            PolyExpr::<F>::Query(q_first.clone(), 0, "q_first".to_owned()),
            unit.selector.unselect(step.uuid()),
        ]);

        unit.polys.push(Poly {
            annotation: "q_first".to_string(),
            expr: poly,
        });

        let mut assignments = vec![F::ZERO; unit.num_rows];
        assignments[0] = F::ONE;
        unit.fixed_assignments.insert(q_first, assignments);
    }

    fn add_q_last<F: Field>(
        &self,
        unit: &mut CompilationUnit<F>,
        step_uuid: Option<StepTypeUUID>,
        q_last: Column,
    ) {
        if let Some(step_uuid) = step_uuid {
            let step = unit.step_types.get(&step_uuid).expect("step not found");

            let poly = PolyExpr::Mul(vec![
                PolyExpr::<F>::Query(q_last.clone(), 0, "q_last".to_owned()),
                unit.selector.unselect(step.uuid()),
            ]);

            unit.polys.push(Poly {
                annotation: "q_last".to_string(),
                expr: poly,
            });
        }

        let mut assignments = vec![F::ZERO; unit.num_rows];
        assignments[unit.num_rows - unit.placement.first_step_height() as usize] = F::ONE;
        unit.fixed_assignments.insert(q_last, assignments);
    }

    fn add_q_last_to_constraint<F: Field>(
        unit: &mut CompilationUnit<F>,
        constraint: PolyExpr<F>,
    ) -> PolyExpr<F> {
        let q_last_column = unit.last_step.clone().expect("last column not found").1;
        let q_last = PolyExpr::<F>::Query(q_last_column, 0, "q_last".to_owned());
        let not_q_last_expr = PolyExpr::Sum(vec![
            PolyExpr::Const(F::ONE),
            PolyExpr::Neg(Box::new(q_last)),
        ]);

        PolyExpr::Mul(vec![not_q_last_expr, constraint])
    }

    fn add_default_columns<F>(&self, unit: &mut CompilationUnit<F>) {
        if let Some(q_enable) = &unit.q_enable {
            unit.columns.push(q_enable.clone())
        }

        if let Some((_, q_first)) = &unit.first_step {
            unit.columns.push(q_first.clone());
        }

        if let Some((_, q_last)) = &unit.last_step {
            unit.columns.push(q_last.clone());
        }
    }

    fn add_halo2_columns<F, TraceArgs>(
        &self,
        unit: &mut CompilationUnit<F>,
        ast: &astCircuit<F, TraceArgs>,
    ) {
        let halo2_advice_columns: Vec<Column> = ast
            .halo2_advice
            .iter()
            .map(|signal| {
                if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    Column::new_halo2_advice(format!("halo2 advice {}", annotation), *signal)
                } else {
                    Column::new_halo2_advice("halo2 advice", *signal)
                }
            })
            .collect();

        let halo2_fixed_columns: Vec<Column> = ast
            .halo2_fixed
            .iter()
            .map(|signal| {
                if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    Column::new_halo2_fixed(format!("halo2 fixed {}", annotation), *signal)
                } else {
                    Column::new_halo2_fixed("halo2 fixed", *signal)
                }
            })
            .collect();

        unit.columns.extend(halo2_advice_columns);
        unit.columns.extend(halo2_fixed_columns);
    }
}
