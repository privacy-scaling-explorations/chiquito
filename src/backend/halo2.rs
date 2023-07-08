use std::{collections::HashMap, hash::Hash};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Cell, Layouter, Region, RegionIndex, Value},
    plonk::{
        Advice, Any, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed, Instance,
        SecondPhase, ThirdPhase, VirtualCells,
    },
    poly::Rotation,
};

use crate::{
    ast::ToField,
    ir::{
        assigments::Assignments,
        Circuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr,
    },
};

#[allow(non_snake_case)]
pub fn chiquito2Halo2<F: Field + From<u64> + Hash>(circuit: Circuit<F>) -> ChiquitoHalo2<F> {
    ChiquitoHalo2::new(circuit)
}

#[derive(Clone, Debug)]
pub struct ChiquitoHalo2<F: Field + From<u64>> {
    pub debug: bool,

    circuit: Circuit<F>,

    advice_columns: HashMap<u32, Column<Advice>>,
    fixed_columns: HashMap<u32, Column<Fixed>>,
    instance_column: Option<Column<Instance>>,
}

impl<F: Field + From<u64> + Hash> ChiquitoHalo2<F> {
    pub fn new(circuit: Circuit<F>) -> ChiquitoHalo2<F> {
        ChiquitoHalo2 {
            debug: true,
            circuit,
            advice_columns: Default::default(),
            fixed_columns: Default::default(),
            instance_column: Default::default(),
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
        if !self.circuit.exposed.is_empty() {
            self.instance_column = Some(meta.instance_column());
        }

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

    pub fn synthesize(&self, layouter: &mut impl Layouter<F>, witness: Option<Assignments<F>>) {
        let _ = layouter.assign_region(
            || "circuit",
            |mut region| {
                self.annotate_circuit(&mut region);

                self.assign_fixed(&mut region, &self.circuit.fixed_assignments)?;

                if let Some(witness) = &witness {
                    self.assign_advice(&mut region, witness)?;
                }

                Ok(())
            },
        );

        for (index, (column, rotation)) in self.circuit.exposed.iter().enumerate() {
            let halo2_column =
                Column::<Any>::from(*self.advice_columns.get(&column.uuid()).unwrap());
            let cell = new_cell(
                halo2_column,
                // For single row cell manager, forward signal rotation is always zero.
                // For max width cell manager, rotation can be non-zero.
                // Offset is 0 + rotation for the first step instance.
                *rotation as usize,
            );
            let _ = layouter.constrain_instance(cell, self.instance_column.unwrap(), index);
        }
    }

    fn assign_advice(&self, region: &mut Region<F>, witness: &Assignments<F>) -> Result<(), Error> {
        for (column, assignments) in witness {
            let column = self.convert_advice_column(column);

            for (offset, value) in assignments.iter().enumerate() {
                region.assign_advice(|| "", column, offset, || Value::known(*value))?;
            }
        }

        Ok(())
    }

    fn assign_fixed(&self, region: &mut Region<F>, fixed: &Assignments<F>) -> Result<(), Error> {
        for (column, values) in fixed {
            let column = self.convert_fixed_column(column);

            for (offset, value) in values.iter().enumerate() {
                region.assign_fixed(|| "", column, offset, || Value::known(*value))?;
            }
        }

        Ok(())
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

    fn convert_advice_column(&self, column: &cColumn) -> Column<Advice> {
        match column.ctype {
            cAdvice | Halo2Advice => *self
                .advice_columns
                .get(&column.uuid())
                .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            _ => panic!("worng column type"),
        }
    }

    fn convert_fixed_column(&self, column: &cColumn) -> Column<Fixed> {
        match column.ctype {
            cFixed | Halo2Fixed => *self
                .fixed_columns
                .get(&column.uuid())
                .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            _ => panic!("worng column type"),
        }
    }
}

#[allow(dead_code)]
// From Plaf Halo2 backend.
// _Cell is a helper struct used for constructing Halo2 Cell.
struct _Cell {
    region_index: RegionIndex,
    row_offset: usize,
    column: Column<Any>,
}
// From Plaf Halo2 backend.
fn new_cell(column: Column<Any>, offset: usize) -> Cell {
    let cell = _Cell {
        region_index: RegionIndex::from(0),
        row_offset: offset,
        column,
    };
    // NOTE: We use unsafe here to construct a Cell, which doesn't have a public constructor.  This
    // helps us set the copy constraints easily (without having to store all assigned cells
    // previously)
    unsafe { std::mem::transmute::<_Cell, Cell>(cell) }
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
