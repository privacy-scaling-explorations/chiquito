use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
        VirtualCells,
    },
    poly::Rotation, halo2curves::ff::PrimeField,
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
use num_bigint::{BigUint, ToBigInt};
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

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: PrimeField, TraceArgs, StepArgs: Clone> {
    debug: bool,
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    // query_index: Counter, 
    c_column_id_to_p_column_index: HashMap<u32, usize>, // chiquito column id doesn't have fixed start; plaf column index starts from 0 for each of witness (advice), fixed, and public types; therefore a mapping is needed to convert chiquito query to plaf query
    advice_index: Counter, // index of witness (advice) column in plaf
    fixed_index: Counter, // index of fixed column in plaf
}

impl<F: PrimeField<Repr = [u8; 32]>, TraceArgs, StepArgs: Clone> ChiquitoPlaf<F, TraceArgs, StepArgs> { // ??? Field doesn't satisfy the Var trait, which requires PartialEq and other traits
    // <Repr = [u8; 32]> is required by `from` function in the following line:
    // cPolyExpr::Halo2Expr(e) => pExpr::from(e)
    // this function converts a halo2 Expression<F> to a polyexen Expr<PlonkVar>
    // F: PrimeField<Repr = [u8; 32] is required
    pub fn new(circuit: cCircuit<F, TraceArgs, StepArgs>, debug: bool) -> ChiquitoPlaf<F, TraceArgs, StepArgs> {
        ChiquitoPlaf {
            debug,
            circuit,
            // query_index: Counter::new(),
            c_column_id_to_p_column_index: HashMap::new(),
            advice_index: Counter::new(),
            fixed_index: Counter::new(),
        }
    }

    pub fn chiquito2Plaf(&mut self) -> Plaf {
        // let mut chiquito_plaf = Self::new(circuit);
        let mut plaf = Plaf::default();

        let mut c_column_id_to_p_column_index = HashMap::<u32, usize>::new();
        let mut advice_index = Counter::new();
        let mut fixed_index = Counter::new();

        // self.convert_and_push_plaf_column(&self.circuit.q_enable, &mut plaf);

        // match &self.circuit.q_first {
        //     Some(cColumn) => {
        //         self.convert_and_push_plaf_column(&cColumn, &mut plaf);
        //     }
        //     None => {}
        // }

        // match &self.circuit.q_last {
        //     Some(cColumn) => {
        //         self.convert_and_push_plaf_column(&cColumn, &mut plaf);
        //     }
        //     None => {}
        // }

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
            for cPoly in &mut self.circuit.polys.iter() {
                let plaf_poly = pPoly {
                    name: cPoly.annotation.clone(),
                    exp: self.convert_plaf_poly(&cPoly.expr, &mut counter),
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
        c_column_id_to_p_column_index: Option<&mut HashMap<u32, usize>>, // the three Option fields need to be all Some or all None; not the best practice but this function is only used interally
        advice_index: Option<&mut Counter>,
        fixed_index: Option<&mut Counter>,
    ) {
        match column.ctype {
            cAdvice => {
                let plaf_witness = ColumnWitness::new( // advice is called witness in plaf
                    column.annotation.clone(),
                    column.phase,
                );
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, advice_index.unwrap()); // will panic if c_column_id_to_p_column_index is Some but advice_index is None
                plaf.columns.witness.push(plaf_witness); 
            }
            cFixed => {
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, fixed_index.unwrap());
                plaf.columns.fixed.push(plaf_fixed);
            }
            Halo2Advice => { // ??? should terminate with error but only phase is missing so I defaulted to 0. is this good?
                let plaf_witness = ColumnWitness::new(
                    column.annotation.clone(),
                    0,
                );
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, advice_index.unwrap());
                plaf.columns.witness.push(plaf_witness);
            }
            Halo2Fixed => { // ??? should terminate with error but nothing is missing. is this good?
                let plaf_fixed = ColumnFixed::new(column.annotation.clone());
                self.add_id_index_mapping(column, c_column_id_to_p_column_index, fixed_index.unwrap());
                plaf.columns.fixed.push(plaf_fixed);
            }
        }
    }

    fn convert_plaf_poly(&self, chiquito_poly: &cPolyExpr<F>, counter: &mut Counter) -> pExpr<PlonkVar> { // !!! not sure if PlonkVar makes sense here
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
                // self.query_index.increment();
                // let index = self.query_index.number();
                // let index = counter.number();
                // counter.increment();
                let index = self.c_column_id_to_p_column_index.get(&column.uuid()).unwrap();
                if self.debug {
                    println!("GET c column id {} match p column index {}", column.uuid(), index);
                    println!("MAP {:#?}", self.c_column_id_to_p_column_index);
                }
                pExpr::Var(PlonkVar::Query(self.convert_plaf_query(column, rotation, annotation, *index)))
            }
        }
    }

    // fn increment_query_index(&mut self) -> usize {
    //     self.query_index.increment();
    //     self.query_index.number()
    // }

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

// #[cfg(test)]
// mod tests {
//     use std::{collections::HashMap, rc::Rc};

//     use halo2_proofs::{
//         arithmetic::Field,
//         circuit::{Layouter, Region, Value, self},
//         plonk::{
//             Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
//             VirtualCells,
//         },
//         poly::Rotation, halo2curves::ff::PrimeField,
//     };

//     use crate::{
//         ast::{query::Queriable, ForwardSignal, InternalSignal, StepType, ToField},
//         compiler::{
//             cell_manager::Placement, step_selector::StepSelector, FixedGenContext, TraceContext,
//             WitnessGenContext,
//         },
//         dsl::StepTypeHandler,
//         ir::{
//             Circuit as cCircuit, Column as cColumn,
//             ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
//             PolyExpr as cPolyExpr,
//         },
//     };

//     // use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
//     // use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
//     use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit};
//     // use mock::test_ctx::TestContext;
//     use num_bigint::{BigUint, ToBigInt};
//     use polyexen::{
//         analyze::{bound_base, find_bounds_poly, Analysis},
//         expr::{ExprDisplay, Expr as pExpr, PlonkVar, ColumnQuery, ColumnKind, Column as pColumn, Var},
//         plaf::{
//             backends::halo2::PlafH2Circuit,
//             frontends::halo2::{gen_witness, get_plaf},
//             Cell, CellDisplay, Plaf, Poly as pPoly, PlafDisplayBaseTOML, PlafDisplayFixedCSV, VarDisplay, ColumnWitness, ColumnFixed, 
//             Lookup as pLookup
//         },
//     };
//     use std::fmt;

//     use std::{
//         fs::File,
//         io::{self, Write},
//     };

//     #[test]
//     fn test_mimc7() {
//         use 
//         let circuit = Mimc7Circuit::new();
//     }

// }
// fn write_files(name: &str, plaf: &Plaf) -> Result<(), io::Error> {
//     let mut base_file = File::create(format!("out/{}.toml", name))?;
//     let mut fixed_file = File::create(format!("out/{}_fixed.csv", name))?;
//     write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
//     write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
//     Ok(())
// }

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
