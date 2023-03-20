use std::marker::PhantomData;

use crate::{
    ast::{Expr, Queriable, StepType, SuperCircuit},
    dsl::StepTypeHandler,
    util::uuid,
};

use self::cell_manager::{CellManager, Placement};

pub mod cell_manager;
pub mod step_selector;

pub struct TraceContext<StepArgs> {
    _p: PhantomData<StepArgs>,
}

impl<StepArgs> TraceContext<StepArgs> {
    pub fn new() -> TraceContext<StepArgs> {
        TraceContext {
            _p: PhantomData::default(),
        }
    }

    pub fn add(&self, step_type: &StepTypeHandler, args: StepArgs) {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct WitnessGenContext<F> {
    _p: PhantomData<F>,
}

impl<F> WitnessGenContext<F> {
    pub fn new() -> WitnessGenContext<F> {
        WitnessGenContext { _p: PhantomData {} }
    }
    pub fn assign(&self, lhs: Queriable, rhs: F) {
        todo!();
    }
}

#[derive(Clone, Debug)]
struct Column {
    pub annotation: String,
    uuid: u32,
}

impl Column {
    fn new(annotation: &str) -> Column {
        Column {
            annotation: annotation.to_string(),
            uuid: uuid(),
        }
    }
}

impl PartialEq for Column {
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
    }
}

impl Eq for Column {}

struct Signal {}

struct Poly<F> {
    annotation: String,
    expr: PolyExpr<F>,
}

enum PolyExpr<F> {
    Const(F),
    Query(Column, u32, String), // column, rotation, annotation
    Sum(Vec<PolyExpr<F>>),
    Mul(Vec<PolyExpr<F>>),
    Neg(Box<PolyExpr<F>>),
    Pow(Box<PolyExpr<F>>, u32),
}

impl<F> PolyExpr<F> {
    fn from_expr(source: Expr<F>) -> PolyExpr<F> {
        match source {
            Expr::Const(c) => PolyExpr::Const(c),
            Expr::Sum(v) => PolyExpr::Sum(v.into_iter().map(|e| PolyExpr::from_expr(e)).collect()),
            Expr::Mul(v) => PolyExpr::Mul(v.into_iter().map(|e| PolyExpr::from_expr(e)).collect()),
            Expr::Neg(v) => PolyExpr::Neg(Box::new(PolyExpr::from_expr(*v))),
            Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(PolyExpr::from_expr(*v)), exp),
            Expr::Query(_) => todo!(),
            Expr::Equal(a, b) => PolyExpr::from_expr(*a - *b),
        }
    }
}

pub struct Circuit<F, StepArgs> {
    placement: Placement<F, StepArgs>,
    columns: Vec<Column>,
    polys: Vec<Poly<F>>,
}

impl<F, StepArgs> Circuit<F, StepArgs> {
    fn place_queriable(&self, step: &StepType<F, StepArgs>, q: Queriable) -> PolyExpr<F> {
        match q {
            Queriable::Internal(signal) => {
                let placement = self.placement.find_internal_signal_placement(step, &signal);
                PolyExpr::Query(placement.column, placement.rotation, "TODO".to_string())
            }
            Queriable::Forward(forward) => {
                let placement = self.placement.get_forward_placement(&forward);
                PolyExpr::Query(placement.column, placement.rotation, "TODO".to_string())
            }
            Queriable::ForwardNext(forward) => {
                let placement = self.placement.get_forward_placement(&forward);
                let super_rotation = placement.rotation + self.placement.step_height(&step);
                PolyExpr::Query(placement.column, super_rotation, "TODO".to_string())
            }
        }
    }

    fn transform_expr(&self, step: &StepType<F, StepArgs>, source: Expr<F>) -> PolyExpr<F> {
        match source {
            Expr::Const(c) => PolyExpr::Const(c),
            Expr::Sum(v) => PolyExpr::Sum(v.into_iter().map(|e| PolyExpr::from_expr(e)).collect()),
            Expr::Mul(v) => PolyExpr::Mul(v.into_iter().map(|e| PolyExpr::from_expr(e)).collect()),
            Expr::Neg(v) => PolyExpr::Neg(Box::new(PolyExpr::from_expr(*v))),
            Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(PolyExpr::from_expr(*v)), exp),
            Expr::Query(q) => self.place_queriable(step, q),
            Expr::Equal(a, b) => PolyExpr::from_expr(*a - *b),
        }
    }
}

pub struct Compiler<CM: CellManager> {
    cell_manager: CM,
}

impl<CM: CellManager> Compiler<CM> {
    pub fn new(cell_manager: CM) -> Compiler<CM> {
        Compiler { cell_manager }
    }

    pub fn compile<F, TraceArgs, StepArgs>(
        &self,
        sc: SuperCircuit<F, TraceArgs, StepArgs>,
    ) -> Circuit<F, StepArgs> {
        let circuit = Circuit::<F, StepArgs> {
            placement: self.cell_manager.place(&sc),
            columns: Vec::new(),
            polys: Vec::new(),
        };

        circuit
    }
}
