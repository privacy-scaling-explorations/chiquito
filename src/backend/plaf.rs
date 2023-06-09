use std::{collections::HashMap, hash::Hash, rc::Rc, ops::BitAnd, os::unix::process};

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::{
    ir::{
        Circuit as cCircuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr as cPolyExpr,
    }, 
    compiler::{
        cell_manager::{
            Placement, CellManager, SingleRowCellManager
        }, 
        step_selector::StepSelector, TraceContext
    }, 
    ast::{StepType, Trace, query::Queriable, InternalSignal, ForwardSignal}, wit_gen::{GenericTraceContext, TraceWitness},
};

use num_bigint::BigUint;
use polyexen::{
    expr::{Column as pColumn, ColumnKind, ColumnQuery, Expr as pExpr, PlonkVar, get_field_p},
    plaf::{ColumnFixed, ColumnWitness, Lookup as pLookup, Plaf, Poly as pPoly, Witness as pWitness},
};

#[allow(non_snake_case)]
pub fn chiquito2Plaf<F: PrimeField<Repr = [u8; 32]>, TraceArgs: Clone, StepArgs: Clone
// , CM: CellManager
>(
    circuit: cCircuit<F, TraceArgs, StepArgs>,
    k: u32,
    debug: bool,
) -> (Plaf, ChiquitoPlafWitGen<F, TraceArgs, StepArgs
    // , CM
    >) {
    let mut chiquito_plaf = ChiquitoPlaf::new(circuit.clone(), debug);
    let plaf = chiquito_plaf.get_plaf(k);
    let mut empty_witness = plaf.gen_empty_witness();
    let wit_gen = ChiquitoPlafWitGen {
        trace: circuit.trace,
        placement: circuit.placement,
        selector: circuit.selector,
        step_types: circuit.step_types,
        plaf_witness: empty_witness,
        c_column_id_to_p_column_index: chiquito_plaf.c_column_id_to_p_column_index,
    };

    (plaf, wit_gen)
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

    pub fn get_plaf(&mut self, k: u32) -> Plaf {
        let mut plaf = Plaf::default();
        let p = get_field_p::<F>();
        plaf.info.p = p;

        plaf.info.num_rows = 2usize.pow(k);

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

pub struct ChiquitoPlafWitGen<F, TraceArgs, StepArgs
// , CM: CellManager
> { // ??? determine the pub/private property of fields later
    pub trace: Option<Rc<Trace<TraceArgs, StepArgs>>>,
    pub placement: Placement<F, StepArgs>,
    // pub cell_manager: CM,
    pub selector: StepSelector<F, StepArgs>,
    pub step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,
    pub plaf_witness: pWitness,
    pub c_column_id_to_p_column_index: HashMap<u32, usize>,
} 

impl <F: PrimeField<Repr = [u8; 32]> + Hash, TraceArgs, StepArgs: Clone
// , CM: CellManager
>
    ChiquitoPlafWitGen<F, TraceArgs, StepArgs
    // , CM
    > 
{
    pub fn generate(&self, input: TraceArgs) -> pWitness {

        let mut plaf_witness = pWitness {
            num_rows: self.plaf_witness.num_rows.clone(),
            columns: self.plaf_witness.columns.clone(),
            witness: self.plaf_witness.witness.clone(),
        };

        if let Some(trace) = &self.trace {
            // let mut ctx = PlafTraceContext::new(self.columns.clone());
            let mut ctx = GenericTraceContext::new(&self.step_types);
            
            trace(&mut ctx, input);

            let witness = ctx.get_witness();

            let mut processor = WitnessProcessor::<F, StepArgs> {
                plaf_witness,
                placement: self.placement.clone(),
                c_column_id_to_p_column_index: self.c_column_id_to_p_column_index.clone(),
                selector: self.selector.clone(),
                step_types: self.step_types.clone(),
                offset: 0,
                // offset: usize,
                cur_step: None,
                // max_offset: 0,
            }; 

            processor.process(witness);
            
            processor.plaf_witness
        } else {
            plaf_witness
        }
    }
}

struct WitnessProcessor<F: PrimeField<Repr = [u8; 32]> + Hash, StepArgs> {
    plaf_witness: pWitness,
    placement: Placement<F, StepArgs>,
    c_column_id_to_p_column_index: HashMap<u32, usize>,
    selector: StepSelector<F, StepArgs>,
    step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,
    offset: usize,
    cur_step: Option<Rc<StepType<F, StepArgs>>>,
    // assigments: Vec<Assignment<F, Advice>>,
    // max_offset: usize,
}

impl<F: PrimeField<Repr = [u8; 32]> + Hash, StepArgs: Clone> WitnessProcessor<F, StepArgs> {
    fn process(&mut self, witness: TraceWitness<F>) {
        for step_instance in witness.step_instances {
            let cur_step = Rc::clone(
                self.step_types
                    .get(&step_instance.step_type_uuid)
                    .expect("step type not found"),
            );

            self.cur_step = Some(Rc::clone(&cur_step));

            for assignment in step_instance.assignments {
                self.assign(assignment.0, assignment.1);
            }

            let selector_assignment = self
                .selector
                .selector_assignment
                .get(&cur_step)
                .expect("selector assignment for step not found");

            for (expr, value) in selector_assignment.iter() {
                match expr {
                    cPolyExpr::Query(column, rotation, annotation) => {
                        let p_column_index = self
                            .c_column_id_to_p_column_index
                            .get(&column.uuid())
                            .expect(format!("plaf column not found for selector expression {}", annotation).as_str());
                        let offset = (self.offset as i32 + rotation) as usize;
                        self.plaf_witness.witness[*p_column_index][offset as usize] = Some(BigUint::from_bytes_le(&value.to_repr()));
                    }
                    _ => panic!("selector expression has wrong cPolyExpr enum type"),
                }
            }

            self.offset += self.placement.step_height(&cur_step) as usize;
        }
    }

    fn assign(&mut self, lhs: Queriable<F>, rhs: F) {
        if let Some(cur_step) = &self.cur_step {
            let (p_column_index, rotation) = self.find_halo2_placement(cur_step, lhs);

            let offset = (self.offset as i32 + rotation) as usize;
            self.plaf_witness.witness[p_column_index][offset as usize] = Some(BigUint::from_bytes_le(&rhs.to_repr()));

            // self.max_offset = self.max_offset.max(offset);
        } else {
            panic!("jarrl assigning outside a step");
        }
    }

    fn find_halo2_placement(
        &self,
        step: &StepType<F, StepArgs>,
        query: Queriable<F>,
    ) -> (usize, i32) {
        match query {
            Queriable::Internal(signal) => self.find_halo2_placement_internal(step, signal),

            Queriable::Forward(forward, next) => {
                self.find_halo2_placement_forward(step, forward, next)
            }

            Queriable::Halo2AdviceQuery(_signal, _rotation) => panic!("Imported Halo2Advice is not supported"),

            _ => panic!("invalid advice assignment on queriable {:?}", query),
        }
    }

    fn find_halo2_placement_internal(
        &self,
        step: &StepType<F, StepArgs>,
        signal: InternalSignal,
    ) -> (usize, i32) {
        let placement = self.placement.find_internal_signal_placement(step, &signal);

        let p_column_index = self
            .c_column_id_to_p_column_index
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("plaf column not found for internal signal {:?}", signal));
    
        (*p_column_index, placement.rotation)
    }

    fn find_halo2_placement_forward(
        &self,
        step: &StepType<F, StepArgs>,
        forward: ForwardSignal,
        next: bool,
    ) -> (usize, i32) {
        let placement = self.placement.get_forward_placement(&forward);

        let super_rotation = placement.rotation
            + if next {
                self.placement.step_height(step) as i32
            } else {
                0
            };

        let p_column_index = self
            .c_column_id_to_p_column_index
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("plaf column not found for forward signal {:?}", forward));

        (*p_column_index, super_rotation)
    }
}

pub fn print_witness(plaf_witness: &pWitness) {
    use polyexen::plaf::WitnessDisplayCSV;
    println!("{}", format!("{}", WitnessDisplayCSV(plaf_witness)));
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
