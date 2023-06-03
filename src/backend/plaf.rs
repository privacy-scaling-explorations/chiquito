use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
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
        Circuit as cCircuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr as cPolyExpr,
    },
};

// use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
// use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit};
// use mock::test_ctx::TestContext;
// use num_bigint::BigUint;
use polyexen::{
    analyze::{bound_base, find_bounds_poly, Analysis},
    expr::{ExprDisplay, Expr as pExpr, PlonkVar, ColumnQuery, ColumnKind, Column as pColumn, Var},
    plaf::{
        backends::halo2::PlafH2Circuit,
        frontends::halo2::{gen_witness, get_plaf},
        Cell, CellDisplay, Plaf, Poly as pPoly, PlafDisplayBaseTOML, PlafDisplayFixedCSV, VarDisplay, ColumnWitness, ColumnFixed, 
        Lookup as pLookup
    },
};
use std::fmt;

use std::{
    fs::File,
    io::{self, Write},
};

// use demo::utils::{alias_replace, gen_empty_block, name_challanges};

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: Field + From<u64>, TraceArgs, StepArgs: Clone> {
    // pub debug: bool,
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    // advice_columns: HashMap<u32, Column<Advice>>,
    // fixed_columns: HashMap<u32, Column<Fixed>>,
    query_index: usize, 
}

impl<F: Field + From<u64>, TraceArgs, StepArgs: Clone> ChiquitoPlaf<F, TraceArgs, StepArgs> { // !!! Field doesn't satisfy the Var trait, which requires PartialEq and other traits
    
    pub fn chiquito2Plaf(circuit: cCircuit<F, TraceArgs, StepArgs>) -> Plaf {
        let mut chiquito_plaf = Self::new(circuit);
        let mut plaf = Plaf::default();

        chiquito_plaf.convert_and_push_plaf_column(&chiquito_plaf.circuit.q_enable, &mut plaf);

        match chiquito_plaf.circuit.q_first {
            Some(cColumn) => {
                chiquito_plaf.convert_and_push_plaf_column(&cColumn, &mut plaf);
            }
            None => {}
        }

        match chiquito_plaf.circuit.q_last {
            Some(cColumn) => {
                chiquito_plaf.convert_and_push_plaf_column(&cColumn, &mut plaf);
            }
            None => {}
        }

        for column in chiquito_plaf.circuit.columns.iter() {
            chiquito_plaf.convert_and_push_plaf_column(column, &mut plaf);
        }

        if !chiquito_plaf.circuit.polys.is_empty() {
            for cPoly in chiquito_plaf.circuit.polys.iter() {
                let plaf_poly = pPoly {
                    name: cPoly.annotation,
                    exp: chiquito_plaf.to_plaf_poly(&cPoly.expr),
                };
                plaf.polys.push(plaf_poly);
            }
        }

        for lookup in chiquito_plaf.circuit.lookups.iter() {
            let v1 = lookup
                .exprs
                .into_iter()
                .map(|(e1, _)| chiquito_plaf.to_plaf_poly(&e1))
                .collect::<Vec<pExpr<PlonkVar>>>();

            let v2 = lookup
                .exprs
                .into_iter()
                .map(|(_, e2)| chiquito_plaf.to_plaf_poly(&e2))
                .collect::<Vec<pExpr<PlonkVar>>>();
            
            let plaf_lookup = pLookup {
                name: lookup.annotation,
                exps: (v1, v2),
            };

            plaf.lookups.push(plaf_lookup);
        }



        plaf
    }

    fn new(circuit: cCircuit<F, TraceArgs, StepArgs>) -> ChiquitoPlaf<F, TraceArgs, StepArgs> {
        ChiquitoPlaf {
            circuit,
            query_index: 0,
        }
    }

    fn convert_and_push_plaf_column(&self, column: &cColumn, plaf: &mut Plaf) {
        match column.ctype {
            cAdvice => {
                let plaf_witness = ColumnWitness::new( // advice is called witness in plaf
                    column.annotation,
                    column.phase,
                );
                plaf.columns.witness.push(plaf_witness); 
            }
            cFixed => {
                let plaf_fixed = ColumnFixed::new(column.annotation);
                plaf.columns.fixed.push(plaf_fixed);
            }
            Halo2Advice => { // ??? should terminate with error but only phase is missing so I defaulted to 0. is this good?
                let plaf_witness = ColumnWitness::new(
                    column.annotation,
                    0,
                );
            }
            Halo2Fixed => { // ??? should terminate with error but nothing is missing. is this good?
                let plaf_fixed = ColumnFixed::new(column.annotation);
                plaf.columns.fixed.push(plaf_fixed);
            }
        }
    }

    fn to_plaf_poly(&self, chiquito_poly: &cPolyExpr<F>) -> pExpr<PlonkVar> { // !!! not sure if PlonkVar makes sense here
        match chiquito_poly {
            cPolyExpr::Const(c) => pExpr::Const(*c),
            cPolyExpr::Sum(es) => {
                let mut iter = es.iter();
                let first = self.to_plaf_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.to_plaf_poly(e))
            }
            cPolyExpr::Mul(es) => {
                let mut iter = es.iter();
                let first = self.to_plaf_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.to_plaf_poly(e))
            }
            cPolyExpr::Neg(e) => -self.to_plaf_poly(e),
            cPolyExpr::Pow(e, n) => {
                if *n == 0 {
                    pExpr::Const(1.field())
                } else {
                    let e = self.to_plaf_poly(e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            cPolyExpr::Halo2Expr(e) => pExpr::from(e),
            cPolyExpr::Query(column, rotation, annotation) => {
                let index = self.increment_query_index();
                pExpr::Var(PlonkVar::Query(self.to_plaf_query(column, rotation, annotation, index)))
            }
        }
    }

    fn increment_query_index(&mut self) -> usize {
        self.query_index += 1;
        self.query_index
    }

    fn to_plaf_query(
        &self,
        column: &cColumn,
        rotation: &i32,
        annotation: &String,
        index: usize, // this is simply the number of queries starting from 0 according to Halo2, so we take an incrementing input
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

fn write_files(name: &str, plaf: &Plaf) -> Result<(), io::Error> {
    let mut base_file = File::create(format!("out/{}.toml", name))?;
    let mut fixed_file = File::create(format!("out/{}_fixed.csv", name))?;
    write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
    write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
    Ok(())
}

// fn gen_circuit_plaf<C: Circuit<Fr> + SubCircuit<Fr>>(name: &str, k: u32, block: &Block<Fr>) {
//     let circuit = C::new_from_block(&block);
//     let mut plaf = get_plaf(k, &circuit).unwrap();
//     name_challanges(&mut plaf);
//     alias_replace(&mut plaf);
//     write_files(name, &plaf).unwrap();
// }

// the following code snippet from Halo2 shows that index is simply an incrementing number
// pub(crate) fn query_advice_index(&mut self, column: Column<Advice>, at: Rotation) -> usize {
//     // Return existing query, if it exists
//     for (index, advice_query) in self.advice_queries.iter().enumerate() {
//         if advice_query == &(column, at) {
//             return index;
//         }
//     }

//     // Make a new query
//     let index = self.advice_queries.len();
//     self.advice_queries.push((column, at));
//     self.num_advice_queries[column.index] += 1;

//     index
// }