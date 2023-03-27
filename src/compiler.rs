use std::marker::PhantomData;

use crate::{
    ast::{query::Queriable, Circuit as astCircuit, Expr, StepType},
    dsl::StepTypeHandler,
    util::uuid,
};

use self::{
    cell_manager::{CellManager, Placement},
    step_selector::StepSelectorBuilder,
};

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

    pub fn add(&self, step: &StepTypeHandler, args: StepArgs) {
        todo!();
    }

    fn start_wg<F>(&self, step: &StepType<F, StepArgs>) -> WitnessGenContext<F> {
        WitnessGenContext { _p: PhantomData }
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
    pub fn assign(&self, lhs: Queriable<F>, rhs: F) {
        todo!();
    }
}

pub struct LookupWitnessGenContext<Args> {
    _p: PhantomData<Args>,
}

impl<Args> LookupWitnessGenContext<Args> {
    pub fn new() -> LookupWitnessGenContext<Args> {
        LookupWitnessGenContext { _p: PhantomData {} }
    }

    pub fn add<F, D: Fn(&WitnessGenContext<F>, Args)>(&self, def: D) {
        todo!();
    }
}

#[derive(Clone, Debug)]
pub struct Column {
    pub annotation: String,
    id: u32,
}

impl Column {
    pub fn new(annotation: &str) -> Column {
        Column {
            annotation: annotation.to_string(),
            id: uuid(),
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

#[derive(Debug)]
struct Poly<F> {
    annotation: String,
    expr: PolyExpr<F>,
}

#[derive(Clone, Debug)]
pub enum PolyExpr<F> {
    Const(F),
    Query(Column, u32, String), // column, rotation, annotation
    Sum(Vec<PolyExpr<F>>),
    Mul(Vec<PolyExpr<F>>),
    Neg(Box<PolyExpr<F>>),
    Pow(Box<PolyExpr<F>>, u32),
}

#[derive(Debug)]
pub struct Circuit<F, StepArgs> {
    placement: Placement<F, StepArgs>,
    columns: Vec<Column>,
    polys: Vec<Poly<F>>,
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

    pub fn compile<F: Clone, TraceArgs, StepArgs>(
        &self,
        sc: astCircuit<F, TraceArgs, StepArgs>,
    ) -> Circuit<F, StepArgs> {
        let placement = self.cell_manager.place(&sc);
        let selector = self.step_selector_builder.build(&sc);
        let mut polys = Vec::<Poly<F>>::new();

        let columns = vec![placement.columns.clone(), selector.columns.clone()].concat();

        for step in sc.step_types.values().into_iter() {
            for cond in step.constraints.iter() {
                let constraint = self.transform_expr(&placement, step, &cond.expr.clone());
                let poly = selector.select(step, &constraint);

                polys.push(Poly {
                    expr: poly,
                    annotation: cond.annotation.clone(),
                })
            }
        }

        Circuit::<F, StepArgs> {
            placement,
            columns,
            polys,
        }
    }

    fn place_queriable<F, StepArgs>(
        &self,
        placement: &Placement<F, StepArgs>,
        step: &StepType<F, StepArgs>,
        q: Queriable<F>,
    ) -> PolyExpr<F> {
        match q {
            Queriable::Internal(signal) => {
                let placement = placement.find_internal_signal_placement(step, &signal);
                PolyExpr::Query(placement.column, placement.rotation, "TODO".to_string())
            }
            Queriable::Forward(forward) => {
                let placement = placement.get_forward_placement(&forward);
                PolyExpr::Query(placement.column, placement.rotation, "TODO".to_string())
            }
            Queriable::ForwardNext(forward) => {
                let step_height = placement.step_height(&step);
                let placement = placement.get_forward_placement(&forward);
                let super_rotation = placement.rotation + step_height;
                PolyExpr::Query(placement.column, super_rotation, "TODO".to_string())
            }
            Queriable::StepTypeNext(_) => todo!(),
            Queriable::_unaccessible(_) => panic!("jarrl"),
        }
    }

    fn transform_expr<F: Clone, StepArgs>(
        &self,
        placement: &Placement<F, StepArgs>,
        step: &StepType<F, StepArgs>,
        source: &Expr<F>,
    ) -> PolyExpr<F> {
        match source.clone() {
            Expr::Const(c) => PolyExpr::Const(c),
            Expr::Sum(v) => PolyExpr::Sum(
                v.into_iter()
                    .map(|e| self.transform_expr(placement, step, &e))
                    .collect(),
            ),
            Expr::Mul(v) => PolyExpr::Mul(
                v.into_iter()
                    .map(|e| self.transform_expr(placement, step, &e))
                    .collect(),
            ),
            Expr::Neg(v) => PolyExpr::Neg(Box::new(self.transform_expr(placement, step, &v))),
            Expr::Pow(v, exp) => {
                PolyExpr::Pow(Box::new(self.transform_expr(placement, step, &v)), exp)
            }
            Expr::Query(q) => self.place_queriable(placement, step, q),
            Expr::Equal(a, b) => {
                let sub = Expr::Sum(vec![*a, Expr::Neg(Box::new(*b))]);
                self.transform_expr(placement, step, &sub)
            }
        }
    }
}
