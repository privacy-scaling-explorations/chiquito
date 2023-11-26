use crate::{
    plonkish::ir::{
        assignments::{AssignmentGenerator, Assignments},
        Circuit, Column, ColumnType, PolyExpr,
    },
    util::UUID,
    wit_gen::{Trace, TraceWitness},
};
use halo2_proofs::arithmetic::Field;
use plonkish_backend::{
    backend::{PlonkishCircuit, PlonkishCircuitInfo},
    frontend::halo2::Halo2Circuit,
    util::expression::{self, rotate::Rotation, Expression, Query},
};
use std::{collections::HashMap, hash::Hash};

// get max phase number + 1 to get number of phases
// for example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output will be 3
fn num_phases(phases: &Vec<usize>) -> usize {
    phases.iter().max().copied().unwrap_or_default() as usize + 1
}

// get number of columns for each phase given a vector of phases
// for example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output vector will be
// [2, 2, 2]
fn num_by_phase(phases: &Vec<usize>) -> Vec<usize> {
    phases.iter().copied().fold(
        vec![0usize; num_phases(phases)],
        |mut num_by_phase, phase| {
            num_by_phase[phase as usize] += 1;
            num_by_phase
        },
    )
}

// This function maps each element in the phases slice to its index within its specific phase.
// For example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output vector will be
// [0, 0, 1, 1, 0, 1].
fn idx_in_phase(phases: &Vec<usize>) -> Vec<usize> {
    phases
        .iter()
        .copied()
        .scan(vec![0; num_phases(phases)], |state, phase| {
            let index = state[phase as usize];
            state[phase as usize] += 1;
            Some(index)
        })
        .collect()
}

// This function maps each element in the phases slice to its index within the circuit, given an
// offset For example, if the phases slice is [0, 1, 0, 1, 2, 2], and the offset is 3, then the
// output vector will be [3, 5, 4, 6, 7, 8], i.e. [3+0+0, 3+2+0, 3+0+1, 3+2+1, 3+4+0, 3+4+1], i.e.
// [offset+phase_offset+index]
fn idx_order_by_phase(phases: &Vec<usize>, offset: usize) -> Vec<usize> {
    phases
        .iter()
        .copied()
        .scan(phase_offsets(phases), |state, phase| {
            let index = state[phase as usize];
            state[phase as usize] += 1;
            Some(offset + index)
        })
        .collect()
}

// get vector of non-selector advice column phases
fn non_selector_advice_phases<F: Field>(circuit: &Circuit<F>) -> Vec<usize> {
    circuit
        .columns
        .iter()
        .filter(|column| {
            column.ctype == ColumnType::Advice && !column.annotation.starts_with("step selector")
        })
        .map(|column| column.phase)
        .collect::<Vec<usize>>()
}

// This function computes the offsets for each phase.
// For example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output vector will be
// [0, 2, 4].
fn phase_offsets(phases: &Vec<usize>) -> Vec<usize> {
    num_by_phase(phases)
        .into_iter()
        .scan(0, |state, num| {
            let offset = *state;
            *state += num;
            Some(offset)
        })
        .collect()
}

pub struct ChiquitoCircuit<F, TraceArgs> {
    // TraceArgs is for trace_gen, which is not used here; we only care about placement
    k: usize,
    instances: Vec<Vec<F>>, /* outter vec has length 1, inner vec has length equal to number of
                             * exposed signals */
    circuit: Circuit<F>,
    num_witness_polys: Vec<usize>,
    advice_idx_in_phase: Vec<usize>,
    assignment_generator: AssignmentGenerator<F, TraceArgs>,
    trace_witness: TraceWitness<F>,
    all_uuids: Vec<UUID>,      // the same order as self.circuit.columns
    fixed_uuids: Vec<UUID>,    // the same order as self.circuit.columns
    selector_uuids: Vec<UUID>, // the same order as self.circuit.columns
    non_selector_advice_uuids: Vec<UUID>, // the same order as self.circuit.columns
    non_selector_advice_uuids_by_phase: HashMap<usize, Vec<UUID>>,
}

impl<F: Field + From<u64> + Hash, TraceArgs> ChiquitoCircuit<F, TraceArgs> {
    pub fn new(
        k: usize,
        circuit: Circuit<F>,
        assignment_generator: AssignmentGenerator<F, TraceArgs>,
        trace_witness: TraceWitness<F>,
    ) -> Self {
        // get all column uuids
        let all_uuids = circuit
            .columns
            .iter()
            .map(|column| column.id)
            .collect::<Vec<UUID>>();

        // get fixed column uuids
        let fixed_uuids = circuit
            .columns
            .iter()
            .filter(|column| column.ctype == ColumnType::Fixed)
            .map(|column| column.id)
            .collect::<Vec<UUID>>();

        // selectors are advice columns whose annotations start with "step selector"
        let selector_uuids = circuit
            .columns
            .iter()
            .filter(|column| {
                column.ctype == ColumnType::Advice && column.annotation.starts_with("step selector")
            })
            .map(|column| column.id)
            .collect::<Vec<UUID>>();

        // non-selector advice columns are advice columns whose annotations don't start with "step
        // selector"
        let non_selector_advice_uuids = circuit
            .columns
            .iter()
            .filter(|column| {
                column.ctype == ColumnType::Advice
                    && !column.annotation.starts_with("step selector")
            })
            .map(|column| column.id)
            .collect::<Vec<UUID>>();

        // check that length of all uuid vectors equals length of all columns
        assert_eq!(
            fixed_uuids.len() + selector_uuids.len() + non_selector_advice_uuids.len(),
            circuit.columns.len()
        );

        // get phase number for all non-selector advice columns
        let non_selector_advice_phases = non_selector_advice_phases(&circuit);
        // get number of witness polynomials for each phase
        let num_witness_polys = num_by_phase(&non_selector_advice_phases);
        let advice_idx_in_phase = idx_in_phase(&non_selector_advice_phases);

        // given non_selector_advice_phases and non_selector_advice_uuids, which have equal lengths,
        // create hashmap of phase to vector of uuids if phase doesn't exist in map, create
        // a new vector and insert it into map if phase exists in map, insert the uuid to
        // the vector associated with the phase
        assert_eq!(
            non_selector_advice_phases.len(),
            non_selector_advice_uuids.len()
        );
        let non_selector_advice_uuids_by_phase = non_selector_advice_phases
            .iter()
            .zip(non_selector_advice_uuids.iter())
            .fold(HashMap::new(), |mut map, (phase, uuid)| {
                map.entry(*phase).or_insert_with(Vec::new).push(*uuid);
                map
            });

        let assignments = assignment_generator.generate_with_witness(trace_witness.clone());

        Self {
            k,
            instances: vec![circuit.instance(&assignments)],
            circuit,
            num_witness_polys,
            advice_idx_in_phase,
            assignment_generator,
            trace_witness,
            all_uuids,
            fixed_uuids,
            selector_uuids,
            non_selector_advice_uuids,
            non_selector_advice_uuids_by_phase,
        }
    }
}

// given column uuid and the vector of all column uuids, get the index or position of the uuid
// has no offset
fn column_idx(column_uuid: UUID, column_uuids: &Vec<UUID>) -> usize {
    column_uuids
        .iter()
        .position(|&uuid| uuid == column_uuid)
        .unwrap()
}

impl<F: Field + Clone + From<u64> + Hash, TraceArgs> PlonkishCircuit<F>
    for ChiquitoCircuit<F, TraceArgs>
{
    fn circuit_info_without_preprocess(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        // there's only one instance column whose length is equal to the number of exposed signals
        // in chiquito circuit `num_instances` is a vector of length 1, because we only have
        // one instance column
        let num_instances = self.instances.iter().map(Vec::len).collect();

        // a vector of zero vectors, each zero vector with 2^k length
        // number of preprocess is equal to number of fixed columns and selector advice columns
        let preprocess_polys =
            vec![vec![F::ZERO; 1 << self.k]; self.fixed_uuids.len() + self.selector_uuids.len()];

        // let column_uuids = column_uuids(&self.circuit);
        let advice_idx = self.advice_idx();
        let constraints = self
            .circuit
            .polys
            .iter()
            .map(|poly| self.convert_expression(poly.expr.clone(), &advice_idx))
            .collect();

        let lookups = self
            .circuit
            .lookups
            .iter()
            .map(|lookup| {
                lookup
                    .exprs
                    .iter()
                    .map(|(input, table)| {
                        (
                            self.convert_expression(input.clone(), &advice_idx),
                            self.convert_expression(table.clone(), &advice_idx),
                        )
                    })
                    .collect()
            })
            .collect();

        Ok(PlonkishCircuitInfo {
            k: self.k,
            num_instances,
            preprocess_polys,
            num_witness_polys: self.num_witness_polys.clone(),
            num_challenges: Default::default(), /* ??? what is challenges used for? This is in
                                                 * halo2 and the PlonkishCircuitInfo struct but
                                                 * not in Chiquito */
            constraints,
            lookups,
            permutations: Default::default(), // Chiquito doesn't have permutations
            max_degree: None,                 // Chiquito doesn't have max degree limit
        })
    }

    // preprocessing has three purposes: 1. batch invert fixed assignments, 2. preprocess selectors,
    // 3. preprocess permutations 1 and 3 don't apply to chiquito; 2 might apply to chiquito but
    // we choose not to implement it yet therefore, we return the same as
    // circuit_info_without_preprocess for now
    fn circuit_info(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        let mut circuit_info = self.circuit_info_without_preprocess()?;
        // make sure all fixed assignments are for fixed column type
        self.circuit
            .fixed_assignments
            .iter()
            .for_each(|(column, _)| match column.ctype {
                ColumnType::Fixed => (),
                _ => panic!("fixed assignments must be for fixed column type"),
            });
        // get assignments Vec<F> by looking up from fixed_assignments and reorder assignment
        // vectors according to self.fixed_uuids finally bind all Vec<F> to a Vec<Vec<F>>
        // here, filter fixed_assigments: HashMap<Column, Vec<F>> by looking up the Column with uuid
        let fixed_assignments = self
            .fixed_uuids
            .iter()
            .map(|uuid| {
                self.circuit
                    .fixed_assignments
                    .get(&self.circuit.columns[column_idx(*uuid, &self.all_uuids)])
                    .unwrap()
                    .clone()
            })
            .collect::<Vec<Vec<F>>>();

        // get selector assignments
        let selector_assignments_unordered: Assignments<F> = self
            .assignment_generator
            .generate_selector_assignments_with_witness(self.trace_witness.clone());
        let selector_assignments = self
            .selector_uuids
            .iter()
            .map(|uuid| {
                selector_assignments_unordered
                    .get(&self.circuit.columns[column_idx(*uuid, &self.all_uuids)])
                    .unwrap()
                    .clone()
            })
            .collect::<Vec<Vec<F>>>();

        // combine fixed assignments and selector assignments
        circuit_info.preprocess_polys = fixed_assignments
            .into_iter()
            .chain(selector_assignments.into_iter())
            .collect();

        Ok(circuit_info)
    }

    fn instances(&self) -> &[Vec<F>] {
        &self.instances
    }

    fn synthesize(
        &self,
        phase: usize,
        _challenges: &[F],
    ) -> Result<Vec<Vec<F>>, plonkish_backend::Error> {
        // get non selector assignments
        let non_selector_assignments_unordered: Assignments<F> = self
            .assignment_generator
            .generate_non_selector_assignments_with_witness(self.trace_witness.clone());
        // length of non selector assignments is equal to number of non selector advice columns of
        // corresponding phase
        let non_selector_assignments = self
            .non_selector_advice_uuids_by_phase
            .get(&phase)
            .expect("synthesize: phase not found")
            .iter()
            .map(|uuid| {
                non_selector_assignments_unordered
                    .get(&self.circuit.columns[column_idx(*uuid, &self.all_uuids)])
                    .unwrap()
                    .clone()
            })
            .collect::<Vec<Vec<F>>>();
        Ok(non_selector_assignments)
    }
}

impl<F: Field, TraceArgs> ChiquitoCircuit<F, TraceArgs> {
    fn advice_idx(self: &ChiquitoCircuit<F, TraceArgs>) -> Vec<usize> {
        let advice_offset = 1 + self.fixed_uuids.len() + self.selector_uuids.len(); // there's only ever 1 instance column for chiquito
        idx_order_by_phase(&non_selector_advice_phases(&self.circuit), advice_offset)
    }

    fn convert_query(
        self: &ChiquitoCircuit<F, TraceArgs>,
        column: Column,
        rotation: i32,
        advice_indx: &Vec<usize>,
    ) -> Expression<F> {
        // if column type is fixed, query column will be determined by column_idx function and
        // self.fixed_uuids if column type is non-selector advice, query column will be
        // determined by column_idx function and self.non_selector_advice_uuids
        // if column type is selector, query column will be determined by column_idx function and
        // self.selector_uuids the order of column number is instance + fixed + selector
        // advice + non-selector advice
        if (column.ctype == ColumnType::Fixed) {
            // there's always only 1 instance column, so the offset is 1
            let column_idx = 1 + column_idx(column.id, &self.fixed_uuids);
            Query::new(column_idx, Rotation(rotation)).into()
        } else if (column.ctype == ColumnType::Advice
            && column.annotation.starts_with("step selector"))
        {
            let column_idx =
                1 + self.fixed_uuids.len() + column_idx(column.id, &self.selector_uuids);
            Query::new(column_idx, Rotation(rotation)).into()
        } else if (column.ctype == ColumnType::Advice
            && !column.annotation.starts_with("step selector"))
        {
            // advice_idx already takes into account of the offset of instance, fixed, and selector
            // columns
            let column_idx = advice_indx[column_idx(column.id, &self.non_selector_advice_uuids)];
            Query::new(column_idx, Rotation(rotation)).into()
        } else {
            panic!("convert_query: column type not supported")
        }
    }

    // query column index will be the column's position in the column uuids vector
    // query column row will be determined by the placement from assignment generator (column and
    // rotation within a step instance) and trace witness (step instance and offset) ast queriable
    // rotation is not multiplied by step height yet placement rotation is rotation within a step
    // instance ir queriable rotation is ast queriable rotation * step height + placement rotation,
    // i.e. super rotation ir queriable rotation is for step type, not step type instance
    // selector exprs are already applied to ir poly exprs
    // do not need to apply step instance offset, i.e. current number of step instances * step
    // height, to ir queriable rotation step instance offset is only for witness assignments,
    // not for constraints or lookups
    fn convert_expression(
        self: &ChiquitoCircuit<F, TraceArgs>,
        poly: PolyExpr<F>,
        advice_idx: &Vec<usize>,
    ) -> Expression<F> {
        match poly {
            PolyExpr::Const(constant) => Expression::Constant(constant),
            PolyExpr::Query((column, rotation, _)) => {
                // let column_idx = column_idx(column.id, &column_uuids);
                // Query::new(column_idx, Rotation(rotation)).into()
                self.convert_query(column, rotation, advice_idx)
            }
            PolyExpr::Sum(expressions) => {
                let mut iter = expressions.iter();
                let first = self.convert_expression(iter.next().unwrap().clone(), advice_idx);
                iter.fold(first, |acc, expression| {
                    acc + self.convert_expression(expression.clone(), advice_idx)
                })
            }
            PolyExpr::Mul(expressions) => {
                let mut iter = expressions.iter();
                let first = self.convert_expression(iter.next().unwrap().clone(), advice_idx);
                iter.fold(first, |acc, expression| {
                    acc * self.convert_expression(expression.clone(), advice_idx)
                })
            }
            PolyExpr::Neg(expression) => -self.convert_expression(*expression, advice_idx), /* might need to convert to Expression::Negated */
            PolyExpr::Pow(expression, pow) => {
                if pow == 0 {
                    Expression::Constant(F::ONE)
                } else {
                    let expression = self.convert_expression(*expression, advice_idx);
                    (1..pow).fold(expression.clone(), |acc, _| acc * expression.clone())
                }
            }
            PolyExpr::Halo2Expr(_) => panic!("halo2 expressions not supported"),
        }
    }
}
