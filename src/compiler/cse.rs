use crate::{
    field::Field,
    poly::{self, cse::replace_expr, Expr, HashResult, VarAssignments},
    sbpir::{query::Queriable, InternalSignal, StepType, SBPIR},
    wit_gen::NullTraceGenerator,
};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

type HashedExpr<F> = Expr<F, Queriable<F>, HashResult>;

pub(super) fn cse<F: Field + Hash>(
    mut circuit: SBPIR<F, NullTraceGenerator>,
) -> SBPIR<F, NullTraceGenerator> {
    let mut queriables = collect_forward_signals(&circuit);

    for (_, step_type) in circuit.step_types.iter_mut() {
        let mut cse = CommonSubexpressionEliminator::new();
        cse.run(step_type, &mut queriables);
    }

    circuit
}

fn collect_forward_signals<F: Field>(circuit: &SBPIR<F, NullTraceGenerator>) -> Vec<Queriable<F>> {
    circuit
        .forward_signals
        .iter()
        .flat_map(|signal| {
            vec![
                Queriable::Forward(*signal, false),
                Queriable::Forward(*signal, true),
            ]
        })
        .collect()
}

#[derive(Debug, Clone)]
struct Config {
    min_degree: Option<usize>,
    min_occurrences: Option<usize>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            min_degree: Some(2),
            min_occurrences: Some(2),
        }
    }
}

struct CommonSubexpressionEliminator<F> {
    initial_pass: bool,
    common_exprs: Vec<HashedExpr<F>>,
    hashed_exprs_map: HashMap<u64, HashedExpr<F>>,
    count_map: HashMap<u64, u32>,
    config: Config,
}

impl<F: Field + Hash> CommonSubexpressionEliminator<F> {
    fn new() -> Self {
        CommonSubexpressionEliminator {
            initial_pass: true,
            common_exprs: Vec::new(),
            hashed_exprs_map: HashMap::new(),
            count_map: HashMap::new(),
            config: Config::default(),
        }
    }

    pub(super) fn run(&mut self, step: &mut StepType<F, ()>, queriables: &mut Vec<Queriable<F>>) {
        while !self.common_exprs.is_empty() || self.initial_pass {
            self.initial_pass = false;
            self.process_step(step, queriables);
        }
    }

    fn process_step(&mut self, step: &mut StepType<F, ()>, queriables: &mut Vec<Queriable<F>>) {
        self.add_internal_queriables(step, queriables);
        let random_assignments = Self::generate_random_assignments(queriables);
        let mut hashed_step = step.with_meta::<HashResult>(&random_assignments);

        self.collect_all_subexpressions(&hashed_step);
        self.identify_common_subexpressions();

        if self.common_exprs.is_empty() {
            return;
        }

        self.replace_common_subexpressions(&mut hashed_step);
        self.reset_state();

        *step = hashed_step.without_meta();
    }

    fn add_internal_queriables(&self, step: &StepType<F, ()>, queriables: &mut Vec<Queriable<F>>) {
        queriables.extend(step.signals.iter().map(|&signal| Queriable::Internal(signal)));
    }

    fn generate_random_assignments(queriables: &[Queriable<F>]) -> VarAssignments<F, Queriable<F>> {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        queriables
            .iter()
            .cloned()
            .map(|q| (q, F::random(&mut rng)))
            .collect()
    }

    fn collect_all_subexpressions(&mut self, step: &StepType<F, HashResult>) {
        let mut all_subexpressions = Vec::new();

        for constraint in &step.constraints {
            Self::collect_subexpressions(&constraint.expr, &mut all_subexpressions);
        }

        for constraint in &step.transition_constraints {
            Self::collect_subexpressions(&constraint.expr, &mut all_subexpressions);
        }

        for expr in all_subexpressions {
            let hash = expr.meta().hash;
            *self.count_map.entry(hash).or_insert(0) += 1;
            self.hashed_exprs_map.entry(hash).or_insert(expr);
        }
    }

    fn collect_subexpressions(
        expr: &HashedExpr<F>,
        subexpressions: &mut Vec<HashedExpr<F>>,
    ) {
        subexpressions.push(expr.clone());

        match expr {
            Expr::Sum(ses, _) | Expr::Mul(ses, _) => {
                ses.iter().for_each(|se| Self::collect_subexpressions(se, subexpressions));
            }
            Expr::Neg(se, _) | Expr::Pow(se, _, _) | Expr::MI(se, _) => {
                Self::collect_subexpressions(se, subexpressions);
            }
            Expr::Const(_, _) | Expr::Query(_, _) | Expr::Halo2Expr(_, _) => {}
        }
    }

    fn identify_common_subexpressions(&mut self) {
        self.common_exprs = self
            .hashed_exprs_map
            .iter()
            .filter_map(|(&hash, expr)| {
                let count = self.count_map.get(&hash).copied().unwrap_or(0);
                let min_occurrences = self.config.min_occurrences.unwrap_or(2) as u32;
                let min_degree = self.config.min_degree.unwrap_or(2);

                if count >= min_occurrences && expr.degree() >= min_degree && !matches!(expr, Expr::MI(_, _)) {
                    Some(expr.clone())
                } else {
                    None
                }
            })
            .collect();

        // sort by degree and number of occurrences - this allows us to replace the best common subexpression
        self.common_exprs.sort_by(|a, b| {
            let a_degree = a.degree();
            let b_degree = b.degree();
            let a_occurrences = self.count_map.get(&a.meta().hash).copied().unwrap_or(0);
            let b_occurrences = self.count_map.get(&b.meta().hash).copied().unwrap_or(0);

            b_degree
                .cmp(&a_degree)
                .then(b_occurrences.cmp(&a_occurrences))
        });
    }

    fn replace_common_subexpressions(&self, hashed_step: &mut StepType<F, HashResult>) {
        let mut signal_factory = SignalFactory::default();
        // we should only replace the best common subexpression and then analyze everything again
        // to find the next best common subexpression
        if let Some(best_expr) = self.common_exprs.first() {
            hashed_step.decomp_constraints(|se| replace_expr(se, best_expr, &mut signal_factory));
        }
    }

    fn reset_state(&mut self) {
        self.count_map.clear();
        self.hashed_exprs_map.clear();
        self.common_exprs.clear();
    }
}

// Basic signal factory.
#[derive(Default)]
struct SignalFactory<F> {
    _p: PhantomData<F>,
}

impl<F> poly::SignalFactory<Queriable<F>> for SignalFactory<F> {
    fn create<S: Into<String>>(&mut self, annotation: S) -> Queriable<F> {
        Queriable::Internal(InternalSignal::new(annotation.into()))
    }
}

#[cfg(test)]
mod test {
    use std::vec;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{poly::{HashResult, ToExpr}, sbpir::{query::Queriable, InternalSignal}};

    use super::CommonSubexpressionEliminator;



    #[test]
    fn test_find_common_expressions() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b = Queriable::Internal(InternalSignal::new("b"));
        let c = Queriable::Internal(InternalSignal::new("c"));
        let d = Queriable::Internal(InternalSignal::new("d"));

        let vars = vec![a.clone(), b.clone(), c.clone(), d.clone()];

        let expr1 = a * b + c;
        let expr2 = d * a * b;
        let expr3 = 1.expr() + a * b + c;

        let cse = CommonSubexpressionEliminator::<Fr>::new();

        let random_assignments = CommonSubexpressionEliminator::generate_random_assignments(&vars);

        let mut hashed_expr1 = expr1.with_meta::<HashResult>(&random_assignments);
        let mut hashed_expr2 = expr2.with_meta::<HashResult>(&random_assignments);
        let mut hashed_expr3 = expr3.with_meta::<HashResult>(&random_assignments);

        

    
    }
}

// For each step type:
//  get common subexpressions (sort by degree and num_occurr)
//  find the best expression to replace (bigger degree and occurrences)
//  create a new auto_signal with the expression
//  find all the occurrences of the

// do everything again until not common subexpressions
