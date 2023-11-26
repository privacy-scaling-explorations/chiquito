use crate::{
    plonkish::ir::{
        assignments::{AssignmentGenerator, Assignments},
        Circuit, PolyExpr,
    },
    util::UUID,
    wit_gen::{Trace, TraceWitness},
};
use halo2_proofs::arithmetic::Field;
use plonkish_backend::{
    backend::{PlonkishCircuit, PlonkishCircuitInfo},
    util::expression::{self, rotate::Rotation, Expression, Query},
};

pub struct ChiquitoCircuit<F, TraceArgs> {
    // TraceArgs is for trace_gen, which is not used here; we only care about placement
    circuit: Circuit<F>,
    assigment_generator: AssignmentGenerator<F, TraceArgs>,
    trace_witness: TraceWitness<F>,
}

// collect vector of all column uuids from the ir circuit
fn column_uuids<F>(circuit: &Circuit<F>) -> Vec<UUID> {
    circuit.columns.iter().map(|column| column.id).collect()
}

// given column uuid and the vector of all column uuids, get the index or position of the uuid
fn column_idx(column_uuid: UUID, column_uuids: &[UUID]) -> usize {
    column_uuids
        .iter()
        .position(|&uuid| uuid == column_uuid)
        .unwrap()
}

// query column index will be the column's position in the column uuids vector
// query column row will be determined by the placement from assignment generator (column and
// rotation within a step instance) and trace witness (step instance and offset) ast queriable
// rotation is not multiplied by step height yet placement rotation is rotation within a step
// instance ir queriable rotation is ast queriable rotation * step height + placement rotation, i.e.
// super rotation ir queriable rotation is for step type, not step type instance
// selector exprs are already applied to ir poly exprs
// do not need to apply step instance offset, i.e. current number of step instances * step height,
// to ir queriable rotation step instance offset is only for witness assignments, not for
// constraints or lookups
fn convert_expression<F: Field>(poly: PolyExpr<F>, column_uuids: &Vec<UUID>) -> Expression<F> {
    match poly {
        PolyExpr::Const(constant) => Expression::Constant(constant),
        PolyExpr::Query((column, rotation, _)) => {
            let column_idx = column_idx(column.id, &column_uuids);
            Query::new(column_idx, Rotation(rotation)).into()
        }
        PolyExpr::Sum(expressions) => {
            let mut iter = expressions.iter();
            let first = convert_expression(iter.next().unwrap().clone(), column_uuids);
            iter.fold(first, |acc, expression| {
                acc + convert_expression(expression.clone(), column_uuids)
            })
        }
        PolyExpr::Mul(expressions) => {
            let mut iter = expressions.iter();
            let first = convert_expression(iter.next().unwrap().clone(), column_uuids);
            iter.fold(first, |acc, expression| {
                acc * convert_expression(expression.clone(), column_uuids)
            })
        }
        PolyExpr::Neg(expression) => -convert_expression(*expression, column_uuids), /* might need to convert to Expression::Negated */
        PolyExpr::Pow(expression, pow) => {
            if pow == 0 {
                Expression::Constant(F::ONE)
            } else {
                let expression = convert_expression(*expression, column_uuids);
                (1..pow).fold(expression.clone(), |acc, _| acc * expression.clone())
            }
        }
        PolyExpr::Halo2Expr(_) => panic!("halo2 expressions not supported"),
    }
}

impl<F: Field, TraceArgs> PlonkishCircuit<F> for ChiquitoCircuit<F, TraceArgs> {
    fn circuit_info_without_preprocess(
        &self,
    ) -> Result<plonkish_backend::backend::PlonkishCircuitInfo<F>, plonkish_backend::Error> {
        let k = 2 ^ 10; // TODO: this is just a make shift number

        // there's only one instance column whose length is equal to the number of exposed signals
        // in chiquito circuit `num_instances` is a vector of length 1, because we only have
        // one instance column
        let num_instances = vec![self.circuit.exposed.len()];

        // a vector of zero vectors, each zero vector with 2^k length; the number of zero vector is
        // set to the number of columns
        let preprocess_polys = vec![vec![F::ZERO; 1 << k]; self.circuit.columns.len()]; // TODO: might need to set this to the number of fixed columns and selector columns

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

        let column_uuids = column_uuids(&self.circuit);
        let constraints = self
            .circuit
            .polys
            .iter()
            .map(|poly| convert_expression(poly.expr.clone(), &column_uuids))
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
                            convert_expression(input.clone(), &column_uuids),
                            convert_expression(table.clone(), &column_uuids),
                        )
                    })
                    .collect()
            })
            .collect();

        Ok(PlonkishCircuitInfo {
            k: k as usize,
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
        self.circuit_info_without_preprocess()
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
