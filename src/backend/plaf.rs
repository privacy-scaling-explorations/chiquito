use std::{collections::HashMap, hash::Hash, rc::Rc};

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::{
    ast::{query::Queriable, ForwardSignal, InternalSignal, SharedSignal, StepType},
    compiler::{cell_manager::Placement, step_selector::StepSelector},
    ir::{
        Circuit as cCircuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr as cPolyExpr,
    },
    wit_gen::TraceWitness,
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
) -> (Plaf, ChiquitoPlafWitGen<F>) {
    let mut chiquito_plaf = ChiquitoPlaf::new(circuit.clone(), debug);
    let plaf = chiquito_plaf.get_plaf(k);
    let empty_witness = plaf.gen_empty_witness();
    let wit_gen = ChiquitoPlafWitGen {
        placement: circuit.placement,
        selector: circuit.selector,
        step_types: circuit.step_types,
        plaf_witness: empty_witness,
        c_column_id_to_p_column_index: chiquito_plaf.c_column_id_to_p_column_index,
    };

    (plaf, wit_gen)
}

#[derive(Clone, Debug)]
pub struct ChiquitoPlaf<F: PrimeField> {
    debug: bool,
    circuit: cCircuit<F>,
    // Chiquito column id doesn't start from zero.
    // Plaf column index starts from 0 for each column type (advice, fixed, and instance).
    // Therefore a mapping is needed to convert chiquito column id to plaf index.
    c_column_id_to_p_column_index: HashMap<u32, usize>,
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
        c_column_id_to_p_column_index: &mut HashMap<u32, usize>,
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
        c_column_id_to_p_column_index: &mut HashMap<u32, usize>,
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

pub struct ChiquitoPlafWitGen<F> {
    placement: Placement,
    selector: StepSelector<F>,
    step_types: HashMap<u32, Rc<StepType<F>>>,
    plaf_witness: pWitness,
    c_column_id_to_p_column_index: HashMap<u32, usize>,
}

impl<F: PrimeField<Repr = [u8; 32]> + Hash> ChiquitoPlafWitGen<F> {
    pub fn generate(&self, witness: Option<TraceWitness<F>>) -> pWitness {
        let plaf_witness = pWitness {
            num_rows: self.plaf_witness.num_rows,
            columns: self.plaf_witness.columns.clone(),
            witness: self.plaf_witness.witness.clone(),
        };

        if let Some(witness) = witness {
            let mut processor = WitnessProcessor::<F> {
                plaf_witness,
                placement: self.placement.clone(),
                c_column_id_to_p_column_index: self.c_column_id_to_p_column_index.clone(),
                selector: self.selector.clone(),
                step_types: self.step_types.clone(),
                offset: 0,
                cur_step: None,
            };

            processor.process(witness);

            processor.plaf_witness
        } else {
            plaf_witness
        }
    }
}

struct WitnessProcessor<F: PrimeField<Repr = [u8; 32]> + Hash> {
    plaf_witness: pWitness,
    placement: Placement,
    c_column_id_to_p_column_index: HashMap<u32, usize>,
    selector: StepSelector<F>,
    step_types: HashMap<u32, Rc<StepType<F>>>,
    offset: usize,
    cur_step: Option<Rc<StepType<F>>>,
}

impl<F: PrimeField<Repr = [u8; 32]> + Hash> WitnessProcessor<F> {
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
                .get(&cur_step.uuid())
                .expect("selector assignment for step not found");

            for (expr, value) in selector_assignment.iter() {
                match expr {
                    cPolyExpr::Query(column, rotation, annotation) => {
                        let p_column_index = self
                            .c_column_id_to_p_column_index
                            .get(&column.uuid())
                            .unwrap_or_else(|| {
                                panic!(
                                    "plaf column not found for selector expression {}",
                                    annotation
                                )
                            });
                        let offset = (self.offset as i32 + rotation) as usize;
                        self.plaf_witness.witness[*p_column_index][offset] =
                            Some(BigUint::from_bytes_le(&value.to_repr()));
                    }
                    _ => panic!("selector expression has wrong cPolyExpr enum type"),
                }
            }

            self.offset += self.placement.step_height(&cur_step) as usize;
        }
    }

    fn assign(&mut self, lhs: Queriable<F>, rhs: F) {
        if let Some(cur_step) = &self.cur_step {
            let (p_column_index, rotation) = self.find_plaf_placement(cur_step, lhs);

            let offset = (self.offset as i32 + rotation) as usize;
            self.plaf_witness.witness[p_column_index][offset] =
                Some(BigUint::from_bytes_le(&rhs.to_repr()));
        } else {
            panic!("jarrl assigning outside a step");
        }
    }

    fn find_plaf_placement(&self, step: &StepType<F>, query: Queriable<F>) -> (usize, i32) {
        match query {
            Queriable::Internal(signal) => self.find_plaf_placement_internal(step, signal),

            Queriable::Forward(forward, next) => {
                self.find_plaf_placement_forward(step, forward, next)
            }

            Queriable::Shared(shared, rot) => self.find_plaf_placement_shared(step, shared, rot),

            Queriable::Halo2AdviceQuery(_signal, _rotation) => {
                panic!("Imported Halo2Advice is not supported")
            }

            _ => panic!("invalid advice assignment on queriable {:?}", query),
        }
    }

    fn find_plaf_placement_internal(
        &self,
        step: &StepType<F>,
        signal: InternalSignal,
    ) -> (usize, i32) {
        let placement = self
            .placement
            .find_internal_signal_placement(step.uuid(), &signal);

        let p_column_index = self
            .c_column_id_to_p_column_index
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("plaf column not found for internal signal {:?}", signal));

        (*p_column_index, placement.rotation)
    }

    fn find_plaf_placement_forward(
        &self,
        step: &StepType<F>,
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

    fn find_plaf_placement_shared(
        &self,
        step: &StepType<F>,
        shared: SharedSignal,
        rot: i32,
    ) -> (usize, i32) {
        let placement = self.placement.get_shared_placement(&shared);

        let super_rotation = placement.rotation + rot * (self.placement.step_height(step) as i32);

        let p_column_index = self
            .c_column_id_to_p_column_index
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("plaf column not found for shared signal {:?}", shared));

        (*p_column_index, super_rotation)
    }
}
