use std::collections::HashMap;

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::ir::{
    Circuit as cCircuit, Column as cColumn,
    ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
    PolyExpr as cPolyExpr,
};

use num_bigint::BigUint;
use polyexen::{
    expr::{Column as pColumn, ColumnKind, ColumnQuery, Expr as pExpr, PlonkVar},
    plaf::{ColumnFixed, ColumnWitness, Lookup as pLookup, Plaf, Poly as pPoly},
};

#[allow(non_snake_case)]
pub fn chiquito2Plaf<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone>(
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    debug: bool,
) -> Plaf {
    let mut chiquito_plaf = ChiquitoPlaf::new(circuit, debug);
    chiquito_plaf.get_plaf()
}

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: PrimeField, TraceArgs, StepArgs: Clone> {
    debug: bool,
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    // chiquito column id doesn't start from zero;
    // plaf column index starts from 0 for each column type (advice, fixed, and instance);
    // therefore a mapping is needed to convert chiquito column id to plaf index
    c_column_id_to_p_column_index: HashMap<u32, usize>,
    advice_index: usize, // index of witness (advice) column in plaf
    fixed_index: usize,  // index of fixed column in plaf
}

impl<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone>
    ChiquitoPlaf<F, TraceArgs, StepArgs>
{
    // <Repr = [u8; 32]> is required by `from` function in the following line:
    // cPolyExpr::Halo2Expr(e) => pExpr::from(e)
    // this function converts a halo2 Expression<F> to a polyexen Expr<PlonkVar>
    // F: PrimeField<Repr = [u8; 32]> is required
    pub fn new(
        circuit: cCircuit<F, TraceArgs, StepArgs>,
        debug: bool,
    ) -> ChiquitoPlaf<F, TraceArgs, StepArgs> {
        ChiquitoPlaf {
            debug,
            circuit,
            c_column_id_to_p_column_index: HashMap::new(),
            advice_index: 0,
            fixed_index: 0,
        }
    }

    pub fn get_plaf(&mut self) -> Plaf {
        let mut plaf = Plaf::default();

        let mut c_column_id_to_p_column_index = HashMap::<u32, usize>::new();
        let mut advice_index = 0;
        let mut fixed_index = 0;

        for column in self.circuit.columns.iter() {
            if self.debug {
                println!("annotation: {}, id: {}", column.annotation, column.id);
            }
            self.convert_and_push_plaf_column(
                column,
                &mut plaf,
                Some(&mut c_column_id_to_p_column_index),
                Some(&mut advice_index),
                Some(&mut fixed_index),
            );
            if self.debug {
                println!("MAP {:#?}", c_column_id_to_p_column_index);
            }
        }

        self.c_column_id_to_p_column_index = c_column_id_to_p_column_index;
        self.advice_index = advice_index;
        self.fixed_index = fixed_index;

        if !self.circuit.polys.is_empty() {
            for c_poly in &mut self.circuit.polys.iter() {
                let plaf_poly = pPoly {
                    name: c_poly.annotation.clone(),
                    exp: self.convert_plaf_poly(&c_poly.expr),
                };
                plaf.polys.push(plaf_poly);
            }
        }

        for lookup in self.circuit.lookups.iter() {
            let v1 = lookup
                .exprs
                .clone()
                .into_iter()
                .map(|(e1, _)| self.convert_plaf_poly(&e1))
                .collect::<Vec<pExpr<PlonkVar>>>();

            let v2 = lookup
                .exprs
                .clone()
                .into_iter()
                .map(|(_, e2)| self.convert_plaf_poly(&e2))
                .collect::<Vec<pExpr<PlonkVar>>>();

            let plaf_lookup = pLookup {
                name: lookup.annotation.clone(),
                exps: (v1, v2),
            };

            plaf.lookups.push(plaf_lookup);
        }

        plaf
    }

    fn convert_and_push_plaf_column(
        &self,
        column: &cColumn,
        plaf: &mut Plaf,
        // the three Option fields need to be all Some or all None;
        // not the best practice but this function is only used interally
        c_column_id_to_p_column_index: Option<&mut HashMap<u32, usize>>,
        advice_index: Option<&mut usize>,
        fixed_index: Option<&mut usize>,
    ) {
        match column.ctype {
            cAdvice => {
                let plaf_witness = ColumnWitness::new(
                    // advice is called witness in plaf
                    column.annotation.clone(),
                    column.phase,
                );
                // will panic if c_column_id_to_p_column_index is Some but advice_index is None
                self.add_id_index_mapping(
                    column,
                    c_column_id_to_p_column_index,
                    advice_index.unwrap(),
                );
                plaf.columns.witness.push(plaf_witness);
            }
            cFixed => {
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(
                    column,
                    c_column_id_to_p_column_index,
                    fixed_index.unwrap(),
                );
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
            cPolyExpr::Const(c) => pExpr::Const(BigUint::from_bytes_le(&c.to_repr())), // PrimeField uses little endian for bytes representation
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
        c_column_id_to_p_column_index: Option<&mut HashMap<u32, usize>>,
        counter: &mut usize,
    ) {
        if let Some(c_column_id_to_p_column_index) = c_column_id_to_p_column_index {
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
    }

    fn convert_plaf_query(
        &self,
        column: &cColumn,
        rotation: &i32,
        _annotation: &str,
        index: usize, // plaf index starts from 0 for each column type
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

// FOR DEBUGGING ONLY: output Plaf's toml representation of the circuit and csv representation of fixed assignments to top level directory
// use std::io::Error;
// pub fn write_files<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone>(
//     name: &str,
//     circuit: cCircuit<F, TraceArgs, StepArgs>
// ) -> Result<(), Error> {
//     use std::env;
//     use crate::backend::plaf::utils::alias_replace;
//     use polyexen::plaf::{PlafDisplayBaseTOML, PlafDisplayFixedCSV};
//     use std::{
//         fs::File,
//         io::Write,
//     };
//     let mut plaf = chiquito2Plaf(circuit, false);
//     alias_replace(&mut plaf);
//     let mut base_file_path = env::current_dir().expect("Failed to get current directory");
//     let mut fixed_file_path = base_file_path.clone();
//     println!("base file path: {:?}", base_file_path);
//     base_file_path.push(format!("output/{}.toml", name));
//     println!("base file path: {:?}", base_file_path);
//     fixed_file_path.push(format!("output/{}_fixed.csv", name));
//     let mut base_file = File::create(&base_file_path)?;
//     let mut fixed_file = File::create(&fixed_file_path)?;
//     write!(base_file, "{}", PlafDisplayBaseTOML(&plaf))?;
//     // fixed assignment file current has nothing in it, because it's not stored in chiquito ir
//     write!(fixed_file, "{}", PlafDisplayFixedCSV(&plaf))?;
//     Ok(())
// }

pub mod utils;
