use std::{collections::HashMap, env, path::PathBuf};

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::{
    ir::{
        Circuit as cCircuit, 
        Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr as cPolyExpr,
    },
    backend::plaf::utils::alias_replace,
};

use num_bigint::BigUint;
use polyexen::{
    expr::{
        Expr as pExpr, PlonkVar, 
        ColumnQuery, ColumnKind, Column as pColumn
    },
    plaf::{
        Plaf, Poly as pPoly, 
        ColumnWitness, ColumnFixed, 
        Lookup as pLookup, 
        PlafDisplayBaseTOML, PlafDisplayFixedCSV
    },
};

use std::{
    fs::File,
    io::{self, Write},
};

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: PrimeField, TraceArgs, StepArgs: Clone> {
    debug: bool,
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    // chiquito column id doesn't start from zero; 
    // plaf column index starts from 0 for each column type (advice, fixed, and instance); 
    // therefore a mapping is needed to convert chiquito column id to plaf index
    c_column_id_to_p_column_index: HashMap<u32, usize>, 
    advice_index: Counter, // index of witness (advice) column in plaf
    fixed_index: Counter, // index of fixed column in plaf
}

impl<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone> ChiquitoPlaf<F, TraceArgs, StepArgs> {
    // <Repr = [u8; 32]> is required by `from` function in the following line:
    // cPolyExpr::Halo2Expr(e) => pExpr::from(e)
    // this function converts a halo2 Expression<F> to a polyexen Expr<PlonkVar>
    // F: PrimeField<Repr = [u8; 32]> is required
    pub fn new(circuit: cCircuit<F, TraceArgs, StepArgs>, debug: bool) -> ChiquitoPlaf<F, TraceArgs, StepArgs> {
        ChiquitoPlaf {
            debug,
            circuit,
            c_column_id_to_p_column_index: HashMap::new(),
            advice_index: Counter::new(),
            fixed_index: Counter::new(),
        }
    }

    pub fn chiquito2Plaf(&mut self) -> Plaf {
        let mut plaf = Plaf::default();

        let mut c_column_id_to_p_column_index = HashMap::<u32, usize>::new();
        let mut advice_index = Counter::new();
        let mut fixed_index = Counter::new();

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
            let mut counter = Counter::new(); 
            for c_poly in &mut self.circuit.polys.iter() {
                let plaf_poly = pPoly {
                    name: c_poly.annotation.clone(),
                    exp: self.convert_plaf_poly(&c_poly.expr, &mut counter),
                };
                plaf.polys.push(plaf_poly);
            }
        }

        for lookup in self.circuit.lookups.iter() {
            let mut counter = Counter::new();

            let v1 = lookup
                .exprs
                .clone()
                .into_iter()
                .map(|(e1, _)| self.convert_plaf_poly(&e1, &mut counter)) // counter needs to be supplied but not really used here
                .collect::<Vec<pExpr<PlonkVar>>>();

            let v2 = lookup
                .exprs
                .clone()
                .into_iter()
                .map(|(_, e2)| self.convert_plaf_poly(&e2, &mut counter))  // counter needs to be supplied but not really used here
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
        advice_index: Option<&mut Counter>,
        fixed_index: Option<&mut Counter>,
    ) {
        match column.ctype {
            cAdvice => {
                let plaf_witness = ColumnWitness::new( // advice is called witness in plaf
                    column.annotation.clone(),
                    column.phase,
                );
                // will panic if c_column_id_to_p_column_index is Some but advice_index is None
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, advice_index.unwrap()); 
                plaf.columns.witness.push(plaf_witness); 
            }
            cFixed => {
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, fixed_index.unwrap());
                plaf.columns.fixed.push(plaf_fixed);
            }
            Halo2Advice => { // ??? QUESTION: should terminate with error but only phase is missing from chiquito imported halo2 advice, so I defaulted phase to 0. is this good?
                let plaf_witness = ColumnWitness::new(
                    column.annotation.clone(),
                    0,
                );
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, advice_index.unwrap());
                plaf.columns.witness.push(plaf_witness);
            }
            Halo2Fixed => { // ??? QUESTION: should terminate with error but nothing is missing from chiquito imported halo2 fixed. is this good?
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, fixed_index.unwrap());
                plaf.columns.fixed.push(plaf_fixed);
            }
        }
    }

    fn convert_plaf_poly(&self, chiquito_poly: &cPolyExpr<F>, counter: &mut Counter) -> pExpr<PlonkVar> {
        match chiquito_poly {
            cPolyExpr::Const(c) => pExpr::Const(BigUint::from_bytes_le(&c.to_repr())), // PrimeField uses little endian for bytes representation
            cPolyExpr::Sum(es) => {
                let mut iter = es.iter();
                let first = self.convert_plaf_poly(iter.next().unwrap(), counter);
                iter.fold(first, |acc, e| acc + self.convert_plaf_poly(e, counter))
            }
            cPolyExpr::Mul(es) => {
                let mut iter = es.iter();
                let first = self.convert_plaf_poly(iter.next().unwrap(), counter);
                iter.fold(first, |acc, e| acc * self.convert_plaf_poly(e, counter))
            }
            cPolyExpr::Neg(e) => -self.convert_plaf_poly(e, counter),
            cPolyExpr::Pow(e, n) => {
                if *n == 0 {
                    pExpr::Const(BigUint::from(1u32))
                } else {
                    let e = self.convert_plaf_poly(e, counter);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            cPolyExpr::Halo2Expr(e) => pExpr::from(e),
            cPolyExpr::Query(column, rotation, annotation) => {
                let index = self.c_column_id_to_p_column_index.get(&column.uuid()).unwrap();
                if self.debug {
                    println!("GET c column id {} match p column index {}", column.uuid(), index);
                    println!("MAP {:#?}", self.c_column_id_to_p_column_index);
                }
                pExpr::Var(PlonkVar::Query(self.convert_plaf_query(column, rotation, annotation, *index)))
            }
        }
    }

    fn add_id_index_mapping(&self, column: &cColumn, c_column_id_to_p_column_index: Option<&mut HashMap<u32, usize>>, counter: &mut Counter) {
        match c_column_id_to_p_column_index {
            Some(c_column_id_to_p_column_index) => {
                c_column_id_to_p_column_index.insert(column.uuid(), counter.number());
                if self.debug {
                    println!("c column id {} match p column index {}", column.uuid(), counter.number());
                }
                counter.increment();
            }
            None => {}
        }
    }

    fn convert_plaf_query(
        &self,
        column: &cColumn,
        rotation: &i32,
        _annotation: &String,
        index: usize, // plaf index starts from 0 for each column type
    ) -> ColumnQuery {
        match column.ctype {
            cAdvice | Halo2Advice => {
                ColumnQuery {
                    column: pColumn {
                        kind: ColumnKind::Witness,
                        index,
                    }, 
                    rotation: rotation.clone(),
                }
            }
            cFixed | Halo2Fixed => {
                ColumnQuery {
                    column: pColumn {
                        kind: ColumnKind::Fixed,
                        index,
                    }, 
                    rotation: rotation.clone(),
                }
            }
        }
    } 
}


#[derive(Clone, Debug)]
pub struct Counter {
    number: usize,
}

impl Counter {
    pub fn new() -> Self {
        Self { number: 0 }
    }

    pub fn increment(&mut self) {
        self.number += 1;
    }

    pub fn number(&self) -> usize {
        self.number
    }
}

pub fn write_files<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone>(
    name: &str, 
    circuit: cCircuit<F, TraceArgs, StepArgs>
) -> Result<(), io::Error> {
    let mut plaf = ChiquitoPlaf::new(circuit, false).chiquito2Plaf();
    alias_replace(&mut plaf);
    let mut base_file_path = env::current_dir().expect("Failed to get current directory");
    let mut fixed_file_path = base_file_path.clone();
    println!("base file path: {:?}", base_file_path);
    base_file_path.push(format!("{}.toml", name));
    println!("base file path: {:?}", base_file_path);
    fixed_file_path.push(format!("{}_fixed.csv", name)); 
    let mut base_file = File::create(&base_file_path)?;
    let mut fixed_file = File::create(&fixed_file_path)?;
    write!(base_file, "{}", PlafDisplayBaseTOML(&plaf))?;
    // fixed assignment file current has nothing in it, because it's not stored in chiquito ir
    write!(fixed_file, "{}", PlafDisplayFixedCSV(&plaf))?;
    Ok(())
}

pub mod utils;
