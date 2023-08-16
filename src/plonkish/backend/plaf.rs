use std::{collections::HashMap, hash::Hash};

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::{
    plonkish::ir::{
        assignments::Assignments,
        Circuit as cCircuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr as cPolyExpr,
    },
    util::UUID,
};

use num_bigint::BigUint;
use polyexen::{
    expr::{get_field_p, Column as pColumn, ColumnKind, ColumnQuery, Expr as pExpr, PlonkVar},
    plaf::{
        ColumnFixed, ColumnPublic, ColumnWitness, CopyC as pCopyC, Lookup as pLookup, Plaf,
        Poly as pPoly, Witness as pWitness,
    },
};

#[allow(non_snake_case)]
pub fn chiquito2Plaf<F: PrimeField<Repr = [u8; 32]>>(
    circuit: cCircuit<F>,
    k: u32,
    debug: bool,
) -> (Plaf, ChiquitoPlafWitGen) {
    let mut chiquito_plaf = ChiquitoPlaf::new(circuit, debug);
    let plaf = chiquito_plaf.get_plaf(k);
    let empty_witness = plaf.gen_empty_witness();
    let wit_gen =
        ChiquitoPlafWitGen::new(empty_witness, chiquito_plaf.c_column_id_to_p_column_index);

    (plaf, wit_gen)
}

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: PrimeField> {
    debug: bool,
    circuit: cCircuit<F>,
    // Chiquito column id doesn't start from zero.
    // Plaf column index starts from 0 for each column type (advice, fixed, and instance).
    // Therefore a mapping is needed to convert chiquito column id to plaf index.
    c_column_id_to_p_column_index: HashMap<UUID, usize>,
}

impl<F: PrimeField<Repr = [u8; 32]>> ChiquitoPlaf<F> {
    pub fn new(circuit: cCircuit<F>, debug: bool) -> ChiquitoPlaf<F> {
        ChiquitoPlaf {
            debug,
            circuit,
            c_column_id_to_p_column_index: HashMap::new(),
        }
    }

    pub fn get_plaf(&mut self, k: u32) -> Plaf {
        let mut plaf = Plaf::default();
        let p = get_field_p::<F>();
        plaf.info.p = p;

        plaf.info.num_rows = 2usize.pow(k);

        let mut c_column_id_to_p_column_index = HashMap::<UUID, usize>::new();
        let mut advice_index = 0;
        let mut fixed_index = 0;

        for column in self.circuit.columns.iter() {
            if self.debug {
                println!("annotation: {}, id: {}", column.annotation, column.id);
            }
            self.convert_and_push_plaf_column(
                column,
                &mut plaf,
                &mut c_column_id_to_p_column_index,
                &mut advice_index,
                &mut fixed_index,
            );
            if self.debug {
                println!("MAP {:#?}", c_column_id_to_p_column_index);
            }
        }

        self.c_column_id_to_p_column_index = c_column_id_to_p_column_index;

        for c_poly in &mut self.circuit.polys.iter() {
            let plaf_poly = pPoly {
                name: c_poly.annotation.clone(),
                exp: self.convert_plaf_poly(&c_poly.expr),
            };
            plaf.polys.push(plaf_poly);
        }

        for lookup in self.circuit.lookups.iter() {
            let exps = lookup.exprs.clone().into_iter().fold(
                (Vec::default(), Vec::default()),
                |mut result, tuple| {
                    result.0.push(self.convert_plaf_poly(&tuple.0));
                    result.1.push(self.convert_plaf_poly(&tuple.1));
                    result
                },
            );

            let plaf_lookup = pLookup {
                name: lookup.annotation.clone(),
                exps,
            };

            plaf.lookups.push(plaf_lookup);
        }

        // Fixed
        let mut fixed: Vec<Vec<Option<BigUint>>> = Vec::with_capacity(plaf.columns.fixed.len());
        for _i in 0..plaf.columns.fixed.len() {
            fixed.push(vec![None; plaf.info.num_rows]);
        }

        for (column, values) in self.circuit.fixed_assignments.clone().into_iter() {
            let column = self
                .c_column_id_to_p_column_index
                .get(&column.uuid())
                .expect("plaf column not found for fixed signal");

            for (offset, value) in values.iter().enumerate() {
                // region.assign_fixed(|| "", *column, offset, || Value::known(value.clone()));
                fixed[*column][offset] = Some(BigUint::from_bytes_le(&value.to_repr()));
            }
        }
        plaf.fixed = fixed;

        if !self.circuit.exposed.is_empty() {
            // Public column not pulled from Chiquito ir, because it's not stored anywhere.
            // Therefore, we create a Plaf public column from scratch.
            let plaf_public = ColumnPublic::new(String::from(
                "exposed forward signal values in first step instance",
            ));
            plaf.columns.public.push(plaf_public);
        }

        for (index, (c_column, rotation)) in self.circuit.exposed.iter().enumerate() {
            let public_column = pColumn {
                kind: ColumnKind::Public,
                index: 0, // Chiquito only has one public column, so the index is always 0.
            };

            let witness_index = self
                .c_column_id_to_p_column_index
                .get(&c_column.uuid())
                .unwrap();

            let witness_column = pColumn {
                kind: ColumnKind::Witness,
                index: *witness_index,
            };

            let copy = pCopyC {
                columns: (public_column, witness_column),
                offsets: vec![(index, *rotation as usize)],
            };

            plaf.copys.push(copy);
        }

        plaf
    }

    fn convert_and_push_plaf_column(
        &self,
        column: &cColumn,
        plaf: &mut Plaf,
        c_column_id_to_p_column_index: &mut HashMap<UUID, usize>,
        advice_index: &mut usize,
        fixed_index: &mut usize,
    ) {
        match column.ctype {
            cAdvice => {
                let plaf_witness = ColumnWitness::new(column.annotation.clone(), column.phase);
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, advice_index);
                plaf.columns.witness.push(plaf_witness);
            }
            cFixed => {
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, fixed_index);
                plaf.columns.fixed.push(plaf_fixed);
            }
            Halo2Advice => {
                panic!("Imported Halo2Advice is not supported");
            }
            Halo2Fixed => {
                panic!("Imported Halo2Fixed is not supported");
            }
        }
    }

    fn convert_plaf_poly(&self, chiquito_poly: &cPolyExpr<F>) -> pExpr<PlonkVar> {
        match chiquito_poly {
            cPolyExpr::Const(c) => pExpr::Const(BigUint::from_bytes_le(&c.to_repr())),
            cPolyExpr::Sum(es) => {
                let mut iter = es.iter();
                let first = self.convert_plaf_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.convert_plaf_poly(e))
            }
            cPolyExpr::Mul(es) => {
                let mut iter = es.iter();
                let first = self.convert_plaf_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.convert_plaf_poly(e))
            }
            cPolyExpr::Neg(e) => -self.convert_plaf_poly(e),
            cPolyExpr::Pow(e, n) => {
                if *n == 0 {
                    pExpr::Const(BigUint::from(1u32))
                } else {
                    let e = self.convert_plaf_poly(e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            cPolyExpr::Halo2Expr(e) => pExpr::from(e),
            cPolyExpr::Query(column, rotation, annotation) => {
                let index = self
                    .c_column_id_to_p_column_index
                    .get(&column.uuid())
                    .unwrap();
                if self.debug {
                    println!(
                        "GET c column id {} match p column index {}",
                        column.uuid(),
                        index
                    );
                    println!("MAP {:#?}", self.c_column_id_to_p_column_index);
                }
                pExpr::Var(PlonkVar::Query(
                    self.convert_plaf_query(column, rotation, annotation, *index),
                ))
            }
        }
    }

    fn add_id_index_mapping(
        &self,
        column: &cColumn,
        c_column_id_to_p_column_index: &mut HashMap<UUID, usize>,
        counter: &mut usize,
    ) {
        c_column_id_to_p_column_index.insert(column.uuid(), *counter);
        if self.debug {
            println!(
                "c column id {} match p column index {}",
                column.uuid(),
                counter
            );
        }
        *counter += 1;
    }

    fn convert_plaf_query(
        &self,
        column: &cColumn,
        rotation: &i32,
        _annotation: &str,
        index: usize, // Plaf index starts from 0 for each column type.
    ) -> ColumnQuery {
        match column.ctype {
            cAdvice => ColumnQuery {
                column: pColumn {
                    kind: ColumnKind::Witness,
                    index,
                },
                rotation: *rotation,
            },
            cFixed => ColumnQuery {
                column: pColumn {
                    kind: ColumnKind::Fixed,
                    index,
                },
                rotation: *rotation,
            },
            Halo2Advice | Halo2Fixed => {
                panic!("Imported Halo2Advice and Halo2Fixed are not supported")
            }
        }
    }
}

pub struct ChiquitoPlafWitGen {
    empty_witness: pWitness,
    c_column_id_to_p_column_index: HashMap<UUID, usize>,
}

impl ChiquitoPlafWitGen {
    fn new(empty_witness: pWitness, c_column_id_to_p_column_index: HashMap<UUID, usize>) -> Self {
        Self {
            empty_witness,
            c_column_id_to_p_column_index,
        }
    }

    pub fn generate<F: PrimeField<Repr = [u8; 32]> + Hash>(
        &self,
        witness: Option<Assignments<F>>,
    ) -> pWitness {
        let mut plaf_witness = pWitness {
            num_rows: self.empty_witness.num_rows,
            columns: self.empty_witness.columns.clone(),
            witness: self.empty_witness.witness.clone(),
        };

        if let Some(witness) = &witness {
            for (column, assignments) in witness {
                let p_column_index = self
                    .c_column_id_to_p_column_index
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("plaf column not found for column {:?}", column));

                for (offset, value) in assignments.iter().enumerate() {
                    plaf_witness.witness[*p_column_index][offset] =
                        Some(BigUint::from_bytes_le(&value.to_repr()));
                }
            }

            plaf_witness
        } else {
            plaf_witness
        }
    }
}
