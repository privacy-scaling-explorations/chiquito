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
use std::hash::Hash;

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
    instance: Vec<F>,
    circuit: Circuit<F>,
    num_witness_polys: Vec<usize>,
    advice_idx_in_phase: Vec<usize>,
    assignment_generator: AssignmentGenerator<F, TraceArgs>,
    trace_witness: TraceWitness<F>,
    fixed_uuids: Vec<UUID>,
    selector_uuids: Vec<UUID>,
    non_selector_advice_uuids: Vec<UUID>,
}

impl<F: Field + From<u64> + Hash, TraceArgs> ChiquitoCircuit<F, TraceArgs> {
    pub fn new(
        k: usize,
        circuit: Circuit<F>,
        assignment_generator: AssignmentGenerator<F, TraceArgs>,
        trace_witness: TraceWitness<F>,
    ) -> Self {
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

        let assignments = assignment_generator.generate_with_witness(trace_witness.clone());

        Self {
            k,
            instance: circuit.instance(&assignments),
            circuit,
            num_witness_polys,
            advice_idx_in_phase,
            assignment_generator,
            trace_witness,
            fixed_uuids,
            selector_uuids,
            non_selector_advice_uuids,
        }
    }
}

// // collect vector of all column uuids from the ir circuit
// fn column_uuids<F>(circuit: &Circuit<F>) -> Vec<UUID> {
//     circuit.columns.iter().map(|column| column.id).collect()
// }

// given column uuid and the vector of all column uuids, get the index or position of the uuid
fn column_idx(column_uuid: UUID, column_uuids: &Vec<UUID>) -> usize {
    column_uuids
        .iter()
        .position(|&uuid| uuid == column_uuid)
        .unwrap()
}

impl<F: Field, TraceArgs> PlonkishCircuit<F> for ChiquitoCircuit<F, TraceArgs> {
    fn circuit_info_without_preprocess(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        // there's only one instance column whose length is equal to the number of exposed signals
        // in chiquito circuit `num_instances` is a vector of length 1, because we only have
        // one instance column
        let num_instances = vec![self.circuit.exposed.len()];

        // a vector of zero vectors, each zero vector with 2^k length; the number of zero vector is
        // set to the number of columns
        let preprocess_polys = vec![vec![F::ZERO; 1 << self.k]; self.circuit.columns.len()]; // TODO: might need to set this to the number of fixed columns and selector columns

        // ??? what is phase used for?
        // get phase number for each column
        let column_phases = self
            .circuit
            .columns
            .iter()
            .map(|column| column.phase)
            .collect::<Vec<usize>>();
        // find the maximum phase and add 1 to get the number of phases, because lowest phase is 0
        let num_phases = column_phases.iter().max().unwrap() + 1;
        // get number of witness polynomials for each phase
        let num_witness_polys = (0..num_phases)
            .map(|phase| column_phases.iter().filter(|&&p| p == phase).count())
            .collect::<Vec<usize>>();

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
            num_witness_polys,
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
        let mut circuit_info = self.circuit_info_without_preprocess();
        // instance is the index 0 column (there's only one instance column ever in chiquito)

        // make sure all fixed assignments are for fixed column type
        self.circuit
            .fixed_assignments
            .iter()
            .for_each(|(column, _)| match column.ctype {
                ColumnType::Fixed => (),
                _ => panic!("fixed assignments must be for fixed column type"),
            });
        // get fixed assignments starting from index 1
        // self.circuit.fixed_assignments.iter().

        // get selector assignments
    }

    fn instances(&self) -> &[Vec<F>] {
        todo!()
    }

    fn synthesize(
        &self,
        round: usize,
        challenges: &[F],
    ) -> Result<Vec<Vec<F>>, plonkish_backend::Error> {
        todo!()
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
        annotation: String,
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
            let column_idx = 1
                + self.fixed_uuids.len()
                + self.selector_uuids.len()
                + column_idx(column.id, &self.non_selector_advice_uuids);
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
            PolyExpr::Query((column, rotation, annotation)) => {
                // let column_idx = column_idx(column.id, &column_uuids);
                // Query::new(column_idx, Rotation(rotation)).into()
                self.convert_query(column, rotation, annotation, advice_idx)
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
