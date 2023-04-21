use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
    halo2curves::FieldExt,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
        VirtualCells,
    },
    poly::Rotation,
};

use crate::{
    ast::{query::Queriable, ForwardSignal, InternalSignal, StepType, ToField},
    compiler::{
        cell_manager::Placement, step_selector::StepSelector, FixedGenContext, TraceContext,
        WitnessGenContext,
    },
    dsl::StepTypeHandler,
    ir::{
        Circuit, Column as cColumn, ColumnType::Advice as cAdvice, ColumnType::Fixed as cFixed,
        ColumnType::Halo2Advice, ColumnType::Halo2Fixed, PolyExpr,
    },
};

#[allow(non_snake_case)]
pub fn chiquito2Halo2<F: FieldExt, TraceArgs, StepArgs: Clone>(
    circuit: Circuit<F, TraceArgs, StepArgs>,
) -> ChiquitoHalo2<F, TraceArgs, StepArgs> {
    ChiquitoHalo2::new(circuit)
}

#[derive(Clone, Debug)]
pub struct ChiquitoHalo2<F: Field, TraceArgs, StepArgs: Clone> {
    pub debug: bool,

    circuit: Circuit<F, TraceArgs, StepArgs>,

    advice_columns: HashMap<u32, Column<Advice>>,
    fixed_columns: HashMap<u32, Column<Fixed>>,
}

impl<F: FieldExt, TraceArgs, StepArgs: Clone> ChiquitoHalo2<F, TraceArgs, StepArgs> {
    pub fn new(circuit: Circuit<F, TraceArgs, StepArgs>) -> ChiquitoHalo2<F, TraceArgs, StepArgs> {
        ChiquitoHalo2 {
            debug: true,
            circuit,
            advice_columns: Default::default(),
            fixed_columns: Default::default(),
        }
    }

    pub fn configure(&mut self, meta: &mut ConstraintSystem<F>) {
        let mut advice_columns = HashMap::<u32, Column<Advice>>::new();
        let mut fixed_columns = HashMap::<u32, Column<Fixed>>::new();

        for column in self.circuit.columns.iter() {
            match column.ctype {
                cAdvice => {
                    let halo2_column = to_halo2_advice(meta, column);
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                cFixed => {
                    let halo2_column = meta.fixed_column();
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Advice => {
                    let halo2_column = column
                        .halo2_advice
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Fixed => {
                    let halo2_column = column
                        .halo2_fixed
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
            }
        }

        self.advice_columns = advice_columns;
        self.fixed_columns = fixed_columns;

        if !self.circuit.polys.is_empty() {
            meta.create_gate("main", |meta| {
                let mut constraints: Vec<(&'static str, Expression<F>)> = Vec::new();

                for poly in self.circuit.polys.iter() {
                    let converted = self.convert_poly(meta, &poly.expr);
                    let annotation = Box::leak(
                        format!("{} => {:?}", poly.annotation, converted).into_boxed_str(),
                    );
                    constraints.push((annotation, converted));
                }

                constraints
            });
        }

        for lookup in self.circuit.lookups.iter() {
            let annotation: &'static str = Box::leak(lookup.annotation.clone().into_boxed_str());
            meta.lookup_any(annotation, |meta| {
                let mut exprs = Vec::new();
                for (src, dest) in lookup.exprs.iter() {
                    exprs.push((self.convert_poly(meta, src), self.convert_poly(meta, dest)))
                }

                exprs
            });
        }
    }

    pub fn synthesize(&self, layouter: &mut impl Layouter<F>, args: TraceArgs) {
        let (advice_assignments, height) = self.synthesize_advice(args);

        let _ = layouter.assign_region(
            || "circuit",
            |mut region| {
                self.annotate_circuit(&mut region);

                let fixed_assignments = self.synthesize_fixed();
                for (column, offset, value) in fixed_assignments.iter() {
                    region.assign_fixed(|| "", *column, *offset, || *value)?;
                }

                for (column, offset, value) in advice_assignments.iter() {
                    region.assign_advice(|| "", *column, *offset, || *value)?;
                }

                if height > 0 {
                    self.default_fixed(&mut region, height);
                }

                Ok(())
            },
        );
    }

    fn synthesize_fixed(&self) -> Vec<Assignment<F, Fixed>> {
        if let Some(fg) = &self.circuit.fixed_gen {
            let mut ctx = FixedGenContextHalo2::<F> {
                assigments: Default::default(),

                max_offset: 0,
            };

            fg(&mut ctx);

            ctx.assigments
        } else {
            vec![]
        }
    }

    fn synthesize_advice(&self, args: TraceArgs) -> (Vec<Assignment<F, Advice>>, usize) {
        if self.debug {
            println!("starting advise generation");
        }

        if let Some(trace) = &self.circuit.trace {
            let mut ctx = TraceContextHalo2::<F, StepArgs> {
                assigments: Default::default(),
                advice_columns: self.advice_columns.clone(),
                placement: self.circuit.placement.clone(),
                selector: self.circuit.selector.clone(),
                step_types: self.circuit.step_types.clone(),
                offset: 0,
                cur_step: None,
                max_offset: 0,
                height: 0,
            };

            trace(&mut ctx, args);

            let height = if ctx.height > 0 {
                ctx.height
            } else {
                ctx.max_offset + 1
            };

            (ctx.assigments, height)
        } else {
            (vec![], 0)
        }
    }

    fn annotate_circuit(&self, region: &mut Region<F>) {
        for column in self.circuit.columns.iter() {
            match column.ctype {
                cAdvice | Halo2Advice => {
                    let halo2_column = self
                        .advice_columns
                        .get(&column.uuid())
                        .expect("advice column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column);
                }
                cFixed | Halo2Fixed => {
                    let halo2_column = self
                        .fixed_columns
                        .get(&column.uuid())
                        .expect("fixed column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column);
                }
            }
        }
    }

    fn default_fixed(&self, region: &mut Region<F>, height: usize) {
        let q_enable = self
            .fixed_columns
            .get(&self.circuit.q_enable.uuid())
            .expect("q_enable column not found");

        for i in 0..height {
            region.assign_fixed(|| "q_enable=1", *q_enable, i, || Value::known(F::one()));
        }

        if let Some(q_first) = self.circuit.q_first.clone() {
            let q_first = self
                .fixed_columns
                .get(&q_first.uuid())
                .expect("q_enable column not found");

            region.assign_fixed(|| "q_first=1", *q_first, 0, || Value::known(F::one()));
        }

        if let Some(q_last) = self.circuit.q_last.clone() {
            let q_last = self
                .fixed_columns
                .get(&q_last.uuid())
                .expect("q_enable column not found");

            region.assign_fixed(
                || "q_first=1",
                *q_last,
                height - 1,
                || Value::known(F::one()),
            );
        }
    }

    fn convert_poly(&self, meta: &mut VirtualCells<'_, F>, src: &PolyExpr<F>) -> Expression<F> {
        match src {
            PolyExpr::Const(c) => Expression::Constant(*c),
            PolyExpr::Sum(es) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.convert_poly(meta, e))
            }
            PolyExpr::Mul(es) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.convert_poly(meta, e))
            }
            PolyExpr::Neg(e) => -self.convert_poly(meta, e),
            PolyExpr::Pow(e, n) => {
                if *n == 0 {
                    Expression::Constant(1.field())
                } else {
                    let e = self.convert_poly(meta, e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            PolyExpr::Halo2Expr(e) => e.clone(),
            PolyExpr::Query(column, rotation, _) => self.convert_query(meta, column, *rotation),
        }
    }

    fn convert_query(
        &self,
        meta: &mut VirtualCells<'_, F>,
        column: &cColumn,
        rotation: i32,
    ) -> Expression<F> {
        match column.ctype {
            cAdvice | Halo2Advice => {
                let c = self
                    .advice_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_advice(*c, Rotation(rotation))
            }
            cFixed | Halo2Fixed => {
                let c = self
                    .fixed_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_fixed(*c, Rotation(rotation))
            }
        }
    }
}

type Assignment<F, CT> = (Column<CT>, usize, Value<F>);

struct TraceContextHalo2<F: Field, StepArgs> {
    advice_columns: HashMap<u32, Column<Advice>>,
    placement: Placement<F, StepArgs>,
    selector: StepSelector<F, StepArgs>,
    step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,

    offset: usize,
    cur_step: Option<Rc<StepType<F, StepArgs>>>,

    assigments: Vec<Assignment<F, Advice>>,

    max_offset: usize,
    height: usize,
}

impl<F: Field, StepArgs: Clone> TraceContextHalo2<F, StepArgs> {
    fn find_halo2_placement(
        &self,
        step: &StepType<F, StepArgs>,
        query: Queriable<F>,
    ) -> (Column<Advice>, i32) {
        match query {
            Queriable::Internal(signal) => self.find_halo2_placement_internal(step, signal),

            Queriable::Forward(forward, next) => {
                self.find_halo2_placement_forward(step, forward, next)
            }

            Queriable::Halo2AdviceQuery(signal, rotation) => (signal.column, rotation),

            _ => panic!("invalid advice assignment on queriable {:?}", query),
        }
    }

    fn find_halo2_placement_internal(
        &self,
        step: &StepType<F, StepArgs>,
        signal: InternalSignal,
    ) -> (Column<Advice>, i32) {
        let placement = self.placement.find_internal_signal_placement(step, &signal);

        let column = self
            .advice_columns
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("column not found for internal signal {:?}", signal));

        (*column, placement.rotation)
    }

    fn find_halo2_placement_forward(
        &self,
        step: &StepType<F, StepArgs>,
        forward: ForwardSignal,
        next: bool,
    ) -> (Column<Advice>, i32) {
        let placement = self.placement.get_forward_placement(&forward);

        let super_rotation = placement.rotation
            + if next {
                self.placement.step_height(step) as i32
            } else {
                0
            };

        let column = self
            .advice_columns
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("column not found for forward signal {:?}", forward));

        (*column, super_rotation)
    }
}

impl<F: Field, StepArgs: Clone> TraceContext<StepArgs> for TraceContextHalo2<F, StepArgs> {
    fn add(&mut self, step: &StepTypeHandler, args: StepArgs) {
        if let Some(cur_step) = &self.cur_step {
            self.offset += self.placement.step_height(cur_step) as usize;
        } else {
            self.offset = 0;
        }

        let cur_step = Rc::clone(
            self.step_types
                .get(&step.uuid())
                .expect("step type not found"),
        );

        self.cur_step = Some(Rc::clone(&cur_step));

        (*cur_step.wg)(self, args);

        // activate selector

        let selector_assignment = self
            .selector
            .selector_assignment
            .get(&cur_step)
            .expect("selector assignment for step not found");

        for (expr, value) in selector_assignment.iter() {
            match expr {
                PolyExpr::Query(column, rot, _) => {
                    let column = self
                        .advice_columns
                        .get(&column.uuid())
                        .expect("selector expression column not found");

                    self.assigments.push((
                        *column,
                        self.offset + *rot as usize,
                        Value::known(*value),
                    ))
                }
                _ => panic!("wrong type of expresion is selector assignment"),
            }
        }
    }

    fn set_height(&mut self, height: usize) {
        self.height = height;
    }
}

impl<F: Field, StepArgs: Clone> WitnessGenContext<F> for TraceContextHalo2<F, StepArgs> {
    fn assign(&mut self, lhs: Queriable<F>, rhs: F) {
        if let Some(cur_step) = &self.cur_step {
            let (column, rotation) = self.find_halo2_placement(cur_step, lhs);

            let offset = (self.offset as i32 + rotation) as usize;
            self.assigments.push((column, offset, Value::known(rhs)));

            self.max_offset = self.max_offset.max(offset);
        } else {
            panic!("jarrl assigning outside a step");
        }
    }
}

struct FixedGenContextHalo2<F: Field> {
    assigments: Vec<Assignment<F, Fixed>>,

    max_offset: usize,
}

impl<F: Field> FixedGenContextHalo2<F> {
    fn find_halo2_placement(query: Queriable<F>) -> (Column<Fixed>, i32) {
        match query {
            Queriable::Halo2FixedQuery(signal, rotation) => (signal.column, rotation),
            _ => panic!("invalid fixed assignment on queriable {:?}", query),
        }
    }
}

impl<F: Field> FixedGenContext<F> for FixedGenContextHalo2<F> {
    fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F) {
        let (column, rotation) = Self::find_halo2_placement(lhs);

        if rotation != 0 {
            panic!("cannot assign fixed value with rotation");
        }

        self.assigments.push((column, offset, Value::known(rhs)));

        self.max_offset = self.max_offset.max(offset);
    }
}

pub fn to_halo2_advice<F: Field>(
    meta: &mut ConstraintSystem<F>,
    column: &cColumn,
) -> Column<Advice> {
    match column.phase {
        0 => meta.advice_column_in(FirstPhase),
        1 => meta.advice_column_in(SecondPhase),
        2 => meta.advice_column_in(ThirdPhase),
        _ => panic!("jarll wrong phase"),
    }
}
