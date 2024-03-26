use crate::{
    plonkish::ir::{assignments::Assignments, Circuit, Column, ColumnType, PolyExpr},
    util::UUID,
};
use halo2_proofs::arithmetic::Field;
use plonkish_backend::{
    backend::{PlonkishCircuit, PlonkishCircuitInfo},
    util::expression::{rotate::Rotation, Expression, Query},
};
use std::{collections::HashMap, hash::Hash};

// get max phase number + 1 to get number of phases
// for example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output will be 3
fn num_phases(phases: &[usize]) -> usize {
    phases.iter().max().copied().unwrap_or_default() + 1
}

// get number of columns for each phase given a vector of phases
// for example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output vector will be
// [2, 2, 2]
fn num_by_phase(phases: &[usize]) -> Vec<usize> {
    phases.iter().copied().fold(
        vec![0usize; num_phases(phases)],
        |mut num_by_phase, phase| {
            num_by_phase[phase] += 1;
            num_by_phase
        },
    )
}

// This function maps each element in the phases slice to its index within the circuit, given an
// offset For example, if the phases slice is [0, 1, 0, 1, 2, 2], and the offset is 3, then the
// output vector will be [3, 5, 4, 6, 7, 8], i.e. [3+0+0, 3+2+0, 3+0+1, 3+2+1, 3+4+0, 3+4+1], i.e.
// [offset+phase_offset+index]
fn idx_order_by_phase(phases: &[usize], offset: usize) -> Vec<usize> {
    phases
        .iter()
        .copied()
        .scan(phase_offsets(phases), |state, phase| {
            let index = state[phase];
            state[phase] += 1;
            Some(offset + index)
        })
        .collect()
}

// get vector of advice column phases
fn advice_phases<F: Field>(circuit: &Circuit<F>) -> Vec<usize> {
    circuit
        .columns
        .iter()
        .filter(|column| column.ctype == ColumnType::Advice)
        .map(|column| column.phase)
        .collect::<Vec<usize>>()
}

// This function computes the offsets for each phase.
// For example, if the phases slice is [0, 1, 0, 1, 2, 2], then the output vector will be
// [0, 2, 4].
fn phase_offsets(phases: &[usize]) -> Vec<usize> {
    num_by_phase(phases)
        .into_iter()
        .scan(0, |state, num| {
            let offset = *state;
            *state += num;
            Some(offset)
        })
        .collect()
}

pub struct ChiquitoHyperPlonkCircuit<F> {
    circuit: ChiquitoHyperPlonk<F>,
    assignments: Option<Assignments<F>>,
}

pub struct ChiquitoHyperPlonk<F> {
    k: usize,
    instances: Vec<Vec<F>>, /* outter vec has length 1, inner vec has length equal to number of
                             * exposed signals */
    chiquito_ir: Circuit<F>,
    num_witness_polys: Vec<usize>,
    all_uuids: Vec<UUID>,    // the same order as self.chiquito_ir.columns
    fixed_uuids: Vec<UUID>,  // the same order as self.chiquito_ir.columns
    advice_uuids: Vec<UUID>, // the same order as self.chiquito_ir.columns
    advice_uuids_by_phase: HashMap<usize, Vec<UUID>>,
}

impl<F: Field + From<u64> + Hash> ChiquitoHyperPlonk<F> {
    fn new(k: usize, circuit: Circuit<F>) -> Self {
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

        // get advice column uuids (including step selectors)
        let advice_uuids = circuit
            .columns
            .iter()
            .filter(|column| column.ctype == ColumnType::Advice)
            .map(|column| column.id)
            .collect::<Vec<UUID>>();

        // check that length of all uuid vectors equals length of all columns
        assert_eq!(
            fixed_uuids.len() + advice_uuids.len(),
            circuit.columns.len()
        );

        // get phase number for all advice columns
        let advice_phases = advice_phases(&circuit);
        // get number of witness polynomials for each phase
        let num_witness_polys = num_by_phase(&advice_phases);

        // given non_selector_advice_phases and non_selector_advice_uuids, which have equal lengths,
        // create hashmap of phase to vector of uuids if phase doesn't exist in map, create
        // a new vector and insert it into map if phase exists in map, insert the uuid to
        // the vector associated with the phase
        assert_eq!(advice_phases.len(), advice_uuids.len());
        let advice_uuids_by_phase = advice_phases.iter().zip(advice_uuids.iter()).fold(
            HashMap::new(),
            |mut map: HashMap<usize, Vec<u128>>, (phase, uuid)| {
                map.entry(*phase).or_default().push(*uuid);
                map
            },
        );

        Self {
            k,
            instances: Vec::default(),
            chiquito_ir: circuit,
            num_witness_polys,
            all_uuids,
            fixed_uuids,
            advice_uuids,
            advice_uuids_by_phase,
        }
    }

    fn set_instance(&mut self, instance: Vec<Vec<F>>) {
        self.instances = instance;
    }
}

impl<F: Field + From<u64> + Hash> ChiquitoHyperPlonkCircuit<F> {
    pub fn new(k: usize, circuit: Circuit<F>) -> Self {
        let chiquito_hyper_plonk = ChiquitoHyperPlonk::new(k, circuit);
        Self {
            circuit: chiquito_hyper_plonk,
            assignments: None,
        }
    }

    pub fn set_assignment(&mut self, assignments: Assignments<F>) {
        let instances = vec![self.circuit.chiquito_ir.instance(&assignments)];
        self.circuit.set_instance(instances);
        self.assignments = Some(assignments);
    }
}

// given column uuid and the vector of all column uuids, get the index or position of the uuid
// has no offset
fn column_idx(column_uuid: UUID, column_uuids: &[UUID]) -> usize {
    column_uuids
        .iter()
        .position(|&uuid| uuid == column_uuid)
        .unwrap()
}

impl<F: Field + Clone + From<u64> + Hash> PlonkishCircuit<F> for ChiquitoHyperPlonkCircuit<F> {
    fn circuit_info_without_preprocess(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        // there's only one instance column whose length is equal to the number of exposed signals
        // in chiquito circuit `num_instances` is a vector of length 1, because we only have
        // one instance column
        let num_instances = self.circuit.instances.iter().map(Vec::len).collect();

        // a vector of zero vectors, each zero vector with 2^k length
        // number of preprocess is equal to number of fixed columns
        let preprocess_polys =
            vec![vec![F::ZERO; 1 << self.circuit.k]; self.circuit.fixed_uuids.len()];

        let advice_idx = self.circuit.advice_idx();
        let constraints: Vec<Expression<F>> = self
            .circuit
            .chiquito_ir
            .polys
            .iter()
            .map(|poly| {
                self.circuit
                    .convert_expression(poly.expr.clone(), &advice_idx)
            })
            .collect();

        let lookups = self
            .circuit
            .chiquito_ir
            .lookups
            .iter()
            .map(|lookup| {
                lookup
                    .exprs
                    .iter()
                    .map(|(input, table)| {
                        (
                            self.circuit.convert_expression(input.clone(), &advice_idx),
                            self.circuit.convert_expression(table.clone(), &advice_idx),
                        )
                    })
                    .collect()
            })
            .collect();

        let max_degree = constraints
            .iter()
            .map(|constraint| constraint.degree())
            .max();

        Ok(PlonkishCircuitInfo {
            k: self.circuit.k,
            num_instances,
            preprocess_polys,
            num_witness_polys: self.circuit.num_witness_polys.clone(),
            num_challenges: vec![0; self.circuit.num_witness_polys.len()],
            constraints,
            lookups,
            permutations: Default::default(), // Chiquito doesn't have permutations
            max_degree,
        })
    }

    // preprocess fixed assignments
    fn circuit_info(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        let mut circuit_info = self.circuit_info_without_preprocess()?;
        // make sure all fixed assignments are for fixed column type
        self.circuit
            .chiquito_ir
            .fixed_assignments
            .iter()
            .for_each(|(column, _)| match column.ctype {
                ColumnType::Fixed => (),
                _ => panic!("fixed assignments must be for fixed column type"),
            });
        // get assignments Vec<F> by looking up from fixed_assignments and reorder assignment
        // vectors according to self.fixed_uuids. finally bind all Vec<F> to a Vec<Vec<F>>.
        // here, get Vec<F> from fixed_assigments: HashMap<Column, Vec<F>> by looking up the Column
        // with uuid
        let fixed_assignments = self
            .circuit
            .fixed_uuids
            .iter()
            .map(|uuid| {
                self.circuit
                    .chiquito_ir
                    .fixed_assignments
                    .get(
                        &self.circuit.chiquito_ir.columns
                            [column_idx(*uuid, &self.circuit.all_uuids)],
                    )
                    .unwrap()
                    .clone()
            })
            .collect::<Vec<Vec<F>>>();

        circuit_info.preprocess_polys = fixed_assignments;

        Ok(circuit_info)
    }

    fn instances(&self) -> &[Vec<F>] {
        &self.circuit.instances
    }

    fn synthesize(
        &self,
        phase: usize,
        _challenges: &[F],
    ) -> Result<Vec<Vec<F>>, plonkish_backend::Error> {
        let assignments = self.assignments.clone().unwrap();

        let advice_assignments = self
            .circuit
            .advice_uuids_by_phase
            .get(&phase)
            .expect("synthesize: phase not found")
            .iter()
            .map(|uuid| {
                assignments
                    .get(
                        &self.circuit.chiquito_ir.columns
                            [column_idx(*uuid, &self.circuit.all_uuids)],
                    )
                    .unwrap()
                    .clone()
            })
            .collect::<Vec<Vec<F>>>();
        Ok(advice_assignments)
    }
}

impl<F: Field> ChiquitoHyperPlonk<F> {
    fn advice_idx(self: &ChiquitoHyperPlonk<F>) -> Vec<usize> {
        let advice_offset = self.fixed_uuids.len();
        idx_order_by_phase(&advice_phases(&self.chiquito_ir), advice_offset)
    }

    fn convert_query(
        self: &ChiquitoHyperPlonk<F>,
        column: Column,
        rotation: i32,
        advice_indx: &[usize],
    ) -> Expression<F> {
        // if column type is fixed, query column will be determined by column_idx function and
        // self.fixed_uuids
        // if column type is advice, query column will be
        // determined by column_idx function and self.advice_uuids
        // advice columns come after fixed columns
        if column.ctype == ColumnType::Fixed {
            let column_idx = column_idx(column.id, &self.fixed_uuids);
            Query::new(column_idx, Rotation(rotation)).into()
        } else if column.ctype == ColumnType::Advice {
            // advice_idx already takes into account of the offset of fixed columns
            let column_idx = advice_indx[column_idx(column.id, &self.advice_uuids)];
            Query::new(column_idx, Rotation(rotation)).into()
        } else {
            panic!("convert_query: column type not supported")
        }
    }

    fn convert_expression(
        self: &ChiquitoHyperPlonk<F>,
        poly: PolyExpr<F>,
        advice_idx: &Vec<usize>,
    ) -> Expression<F> {
        match poly {
            PolyExpr::Const(constant) => Expression::Constant(constant),
            PolyExpr::Query((column, rotation, _)) => {
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
            PolyExpr::MI(_) => panic!("MI expressions not supported"),
        }
    }
}
