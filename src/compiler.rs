use core::fmt::Debug;
use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{
        query::Queriable, Circuit as astCircuit, Expr, FixedGen, ImportedHalo2Advice,
        ImportedHalo2Fixed, Lookup, StepType, Trace,
    },
    dsl::StepTypeHandler,
    util::uuid,
};

use self::{
    cell_manager::{CellManager, Placement},
    step_selector::{StepSelector, StepSelectorBuilder},
};

use halo2_proofs::{arithmetic::Field, plonk::Expression};

pub mod cell_manager;
pub mod step_selector;

pub trait TraceContext<StepArgs> {
    fn add(&mut self, step: &StepTypeHandler, args: StepArgs);
}

pub trait WitnessGenContext<F> {
    fn assign(&mut self, lhs: Queriable<F>, rhs: F);
}

pub trait FixedGenContext<F> {
    fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F);
}

#[derive(Clone, Debug)]
pub enum ColumnType {
    Advice,
    Fixed,
    Halo2Advice,
    Halo2Fixed,
}

#[derive(Clone, Debug)]
pub struct Column {
    pub annotation: String,

    pub ctype: ColumnType,
    pub halo2_advice: Option<ImportedHalo2Advice>,
    pub halo2_fixed: Option<ImportedHalo2Fixed>,

    pub phase: usize,

    id: u32,
}

impl Column {
    pub fn advice<A: Into<String>>(annotation: A, phase: usize) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            ctype: ColumnType::Advice,
            phase,
            halo2_advice: None,
            halo2_fixed: None,
        }
    }

    pub fn fixed(annotation: &str) -> Column {
        Column {
            annotation: annotation.to_string(),
            id: uuid(),
            ctype: ColumnType::Fixed,
            phase: 0,
            halo2_advice: None,
            halo2_fixed: None,
        }
    }

    pub fn new_halo2_advice<A: Into<String>>(
        annotation: A,
        halo2_advice: ImportedHalo2Advice,
    ) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            phase: 0,
            ctype: ColumnType::Halo2Advice,
            halo2_advice: Some(halo2_advice),
            halo2_fixed: None,
        }
    }

    pub fn new_halo2_fixed<A: Into<String>>(
        annotation: A,
        halo2_fixed: ImportedHalo2Fixed,
    ) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            phase: 0,
            ctype: ColumnType::Halo2Fixed,
            halo2_advice: None,
            halo2_fixed: Some(halo2_fixed),
        }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }
}

impl PartialEq for Column {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Column {}

#[derive(Clone)]
pub struct Poly<F> {
    pub annotation: String,
    pub expr: PolyExpr<F>,
}

impl<F: Debug> Debug for Poly<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => {:?}", self.annotation, self.expr)
    }
}

#[derive(Clone)]
pub enum PolyExpr<F> {
    Const(F),
    Query(Column, i32, String), // column, rotation, annotation
    Sum(Vec<PolyExpr<F>>),
    Mul(Vec<PolyExpr<F>>),
    Neg(Box<PolyExpr<F>>),
    Pow(Box<PolyExpr<F>>, u32),
    Halo2Expr(Expression<F>),
}

impl<F: Debug> Debug for PolyExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let joiner = |list: &Vec<PolyExpr<F>>, sep: &str| {
            list.iter()
                .map(|v| format!("{:?}", v))
                .collect::<Vec<String>>()
                .join(sep)
        };

        match self {
            Self::Const(arg0) => write!(f, "{:?}", arg0),
            Self::Query(_, _, annotation) => write!(f, "`{}`", annotation),
            Self::Sum(arg0) => write!(f, "({})", joiner(arg0, " + ")),
            Self::Mul(arg0) => write!(f, "({})", joiner(arg0, " * ")),
            Self::Neg(arg0) => write!(f, "(-{:?})", arg0),
            Self::Pow(arg0, arg1) => f.debug_tuple("Pow").field(arg0).field(arg1).finish(),
            Self::Halo2Expr(expr) => write!(f, "{:?}", expr),
        }
    }
}

impl<F: Clone> PolyExpr<F> {
    fn rotate(&self, rot: i32) -> PolyExpr<F> {
        match self {
            PolyExpr::Const(_) => (*self).clone(),
            PolyExpr::Query(c, orig_rot, annotation) => PolyExpr::Query(
                c.clone(),
                orig_rot + rot,
                format!("rot[{}, {}]", rot, annotation),
            ),
            PolyExpr::Sum(v) => PolyExpr::Sum(v.iter().map(|e| e.rotate(rot)).collect()),
            PolyExpr::Mul(v) => PolyExpr::Mul(v.iter().map(|e| e.rotate(rot)).collect()),
            PolyExpr::Neg(v) => PolyExpr::Neg(Box::new(v.rotate(rot))),
            PolyExpr::Pow(v, exp) => PolyExpr::Pow(Box::new(v.rotate(rot)), *exp),
            PolyExpr::Halo2Expr(_) => panic!("jarrl: cannot rotate polyexpr that contains halo2"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PolyLookup<F> {
    pub exprs: Vec<(PolyExpr<F>, PolyExpr<F>)>,
}

#[derive(Debug)]
struct CompilationUnit<F, StepArgs> {
    placement: Placement<F, StepArgs>,
    selector: StepSelector<F, StepArgs>,
    columns: Vec<Column>,
    steps: HashMap<u32, Rc<StepType<F, StepArgs>>>,
    annotations: HashMap<u32, String>,
    polys: Vec<Poly<F>>,
    lookups: Vec<PolyLookup<F>>,
}

impl<F, StepArgs> CompilationUnit<F, StepArgs> {
    fn find_halo2_advice(&self, to_find: ImportedHalo2Advice) -> Option<Column> {
        for column in self.columns.iter() {
            match column.halo2_advice {
                Some(advice) => {
                    if advice == to_find {
                        return Some(column.clone());
                    }
                }
                _ => {}
            }
        }

        None
    }

    fn find_halo2_fixed(&self, to_find: ImportedHalo2Fixed) -> Option<Column> {
        for column in self.columns.iter() {
            match column.halo2_fixed {
                Some(fixed) => {
                    if fixed == to_find {
                        return Some(column.clone());
                    }
                }
                _ => {}
            }
        }

        None
    }
}

#[derive(Clone)]
pub struct Circuit<F, TraceArgs, StepArgs> {
    pub placement: Placement<F, StepArgs>,
    pub selector: StepSelector<F, StepArgs>,
    pub columns: Vec<Column>,
    pub polys: Vec<Poly<F>>,
    pub lookups: Vec<PolyLookup<F>>,
    pub step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,

    pub q_enable: Column,
    pub q_first: Option<Column>,
    pub q_last: Option<Column>,

    pub trace: Option<Rc<Trace<TraceArgs, StepArgs>>>,
    pub fixed_gen: Option<Rc<FixedGen<F>>>,
}

impl<F: Debug, TraceArgs, StepArgs: Debug> Debug for Circuit<F, TraceArgs, StepArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Circuit")
            .field("placement", &self.placement)
            .field("columns", &self.columns)
            .field("polys", &self.polys)
            .field("lookups", &self.lookups)
            .finish()
    }
}

pub struct Compiler<CM: CellManager, SSB: StepSelectorBuilder> {
    cell_manager: CM,
    step_selector_builder: SSB,
}

impl<CM: CellManager, SSB: StepSelectorBuilder> Compiler<CM, SSB> {
    pub fn new(cell_manager: CM, step_selector_builder: SSB) -> Compiler<CM, SSB> {
        Compiler {
            cell_manager,
            step_selector_builder,
        }
    }

    pub fn compile<F: Field + Clone, TraceArgs, StepArgs>(
        &self,
        sc: &mut astCircuit<F, TraceArgs, StepArgs>,
    ) -> Circuit<F, TraceArgs, StepArgs> {
        let annotations: HashMap<u32, String> = {
            let mut acc = sc.annotations.clone();
            for step in sc.step_types.values() {
                acc.extend(step.annotations.clone());
            }

            acc
        };
        sc.annotations = annotations.clone();

        let placement = self.cell_manager.place(&sc);
        let selector = self.step_selector_builder.build(&sc);
        let polys = Vec::<Poly<F>>::new();
        let lookups = Vec::<PolyLookup<F>>::new();

        let halo2_advice_columns: Vec<Column> = sc
            .halo2_advice
            .iter()
            .map(|signal| {
                if let Some(annotation) = sc.annotations.get(&signal.uuid()) {
                    Column::new_halo2_advice(format!("halo2 advice {}", annotation), *signal)
                } else {
                    Column::new_halo2_advice("halo2 advice", *signal)
                }
            })
            .collect();

        let halo2_fixed_columns: Vec<Column> = sc
            .halo2_fixed
            .iter()
            .map(|signal| {
                if let Some(annotation) = sc.annotations.get(&signal.uuid()) {
                    Column::new_halo2_fixed(format!("halo2 fixed {}", annotation), *signal)
                } else {
                    Column::new_halo2_fixed("halo2 fixed", *signal)
                }
            })
            .collect();

        let columns = vec![
            placement.columns.clone(),
            selector.columns.clone(),
            halo2_advice_columns,
            halo2_fixed_columns,
        ]
        .concat();

        let mut unit = CompilationUnit {
            placement,
            selector,
            polys,
            lookups,
            annotations,
            columns,
            steps: sc.step_types.clone(),
        };

        for step in sc.step_types.values() {
            self.compile_step(&mut unit, step);
        }

        let q_enable = Column {
            annotation: "q_enable".to_owned(),
            ctype: ColumnType::Fixed,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: uuid(),
        };

        unit.columns.push(q_enable.clone());

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

        let q_first = if let Some(step_type) = sc.first_step {
            let q_first = Column {
                annotation: "q_first".to_owned(),
                ctype: ColumnType::Fixed,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: uuid(),
            };
            unit.columns.push(q_first.clone());

            let step = unit.steps.get(&step_type.uuid()).expect("step not found");

            let poly = PolyExpr::Mul(vec![
                PolyExpr::<F>::Query(q_first.clone(), 0, "q_first".to_owned()),
                unit.selector.unselect(step),
            ]);

            unit.polys.push(Poly {
                annotation: "q_first".to_string(),
                expr: poly,
            });

            Some(q_first)
        } else {
            None
        };

        let q_last = if let Some(step_type) = sc.last_step {
            let q_last = Column {
                annotation: "q_last".to_owned(),
                ctype: ColumnType::Fixed,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: uuid(),
            };
            unit.columns.push(q_last.clone());

            let step = unit.steps.get(&step_type.uuid()).expect("step not found");

            let poly = PolyExpr::Mul(vec![
                PolyExpr::<F>::Query(q_last.clone(), 0, "q_last".to_owned()),
                unit.selector.unselect(step),
            ]);

            unit.polys.push(Poly {
                annotation: "q_last".to_string(),
                expr: poly,
            });

            Some(q_last)
        } else {
            None
        };

        Circuit::<F, TraceArgs, StepArgs> {
            placement: unit.placement,
            selector: unit.selector,
            columns: unit.columns,
            polys: unit.polys,
            lookups: unit.lookups,
            step_types: unit.steps,
            q_enable,
            q_first,
            q_last,

            trace: sc.trace.as_ref().map(|v| Rc::clone(v)),
            fixed_gen: sc.fixed_gen.as_ref().map(|v| Rc::clone(v)),
        }
    }

    fn compile_step<F: Clone + Debug, StepArgs>(
        &self,
        unit: &mut CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
    ) {
        let step_annotation = unit
            .annotations
            .get(&step.uuid())
            .unwrap_or(&"??".to_string())
            .to_owned();

        for constr in step.constraints.iter() {
            let constraint = self.transform_expr(unit, step, &constr.expr.clone());
            let poly = unit.selector.select(step, &constraint);

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
            let poly = unit.selector.select(step, &constraint);

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
                exprs: lookup
                    .exprs
                    .iter()
                    .map(|(src, dest)| {
                        let src_poly = self.transform_expr(unit, step, src);
                        let dest_poly = self.transform_expr(unit, step, dest);
                        let src_selected = unit.selector.select(step, &src_poly);

                        (src_selected, dest_poly)
                    })
                    .collect(),
            };

            unit.lookups.push(poly_lookup);
        }
    }

    fn place_queriable<F: Clone, StepArgs>(
        &self,
        unit: &CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
        q: Queriable<F>,
    ) -> PolyExpr<F> {
        match q {
            Queriable::Internal(signal) => {
                let placement = unit.placement.find_internal_signal_placement(step, &signal);

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
                let placement = unit.placement.get_forward_placement(&forward);

                let super_rotation = placement.rotation
                    + if next {
                        unit.placement.step_height(&step) as i32
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
            Queriable::StepTypeNext(step_type_handle) => {
                let super_rotation = unit.placement.step_height(&step);
                let dest_step = unit
                    .steps
                    .get(&step_type_handle.uuid())
                    .expect("step not found");

                unit.selector.next_expr(dest_step, super_rotation)
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

    fn transform_expr<F: Clone, StepArgs>(
        &self,
        unit: &CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
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
            Expr::Query(q) => self.place_queriable(&unit, step, q),
            Expr::Halo2Expr(expr) => PolyExpr::Halo2Expr(expr),
        }
    }
}
