use std::{collections::HashMap, fmt::Debug, rc::Rc};

use halo2_proofs::plonk::Expression;

use crate::{
    ast::{FixedGen, ImportedHalo2Advice, ImportedHalo2Fixed, StepType, Trace},
    compiler::{cell_manager::Placement, step_selector::StepSelector},
    util::uuid,
};

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

    pub(crate) id: u32,
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
    pub fn rotate(&self, rot: i32) -> PolyExpr<F> {
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
    pub annotation: String,
    pub exprs: Vec<(PolyExpr<F>, PolyExpr<F>)>,
}
