use crate::{
    field::Field,
    poly::{self, cse::replace_common_subexprs, Expr, HashResult, VarAssignments},
    sbpir::{query::Queriable, InternalSignal, SBPIR},
    wit_gen::NullTraceGenerator,
};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

pub(super) fn cse<F: Field + Hash>(
    mut circuit: SBPIR<F, NullTraceGenerator>,
) -> SBPIR<F, NullTraceGenerator> {
    // for each step in the circuit we collect the exprs in the constraints
    // and the queriables for that step and run CSE
    for (_, step_type) in circuit.step_types.iter_mut() {
        let exprs = step_type
            .constraints
            .iter()
            .map(|c| c.expr.clone())
            .collect::<Vec<_>>();

        let mut queriables: Vec<Queriable<F>> = Vec::new();
        for signal in circuit.forward_signals.iter() {
            queriables.push(Queriable::Forward(signal.clone(), false));
            queriables.push(Queriable::Forward(signal.clone(), true));
        }
        for signal in step_type.signals.iter() {
            queriables.push(Queriable::Internal(signal.clone()));
        }

        let mut cse: CSE<F, Queriable<F>> = CSE::new();
        cse.run(&exprs, &queriables);

        let mut signal_factory = SignalFactory::default();

        let common_ses = cse
            .common_exprs
            .iter()
            .map(|ce| ce.clone())
            .collect::<Vec<_>>();

        step_type.decomp_constraints(|expr| {
            replace_common_subexprs(
                expr.clone(),
                &common_ses,
                &cse.random_assignments,
                &mut signal_factory,
            )
        })
    }

    circuit
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

struct CSE<F, V> {
    random_assignments: VarAssignments<F, V>,

    common_exprs: Vec<Expr<F, V, HashResult>>,

    hashed_exprs_map: HashMap<u64, Expr<F, V, HashResult>>,
    count_map: HashMap<u64, u32>,

    config: Config,
}

impl<F: Field + Hash, V: Debug + Clone + Eq + Hash> CSE<F, V> {
    pub(super) fn run(&mut self, exprs: &Vec<Expr<F, V, ()>>, queriables: &[V]) {
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        self.random_assignments = queriables
            .iter()
            .cloned()
            .map(|q| (q, F::random(&mut rng)))
            .collect();

        let mut all_hashed_exprs: Vec<Expr<F, V, HashResult>> = Vec::new();

        for expr in exprs {
            let subexprs = self.hash_recursive(expr);
            all_hashed_exprs.extend(subexprs);
        }

        self.count_expression_occurrences(&all_hashed_exprs);
        self.collect_common_expressions();
    }

    fn new() -> Self {
        CSE {
            random_assignments: VarAssignments::default(),
            common_exprs: Vec::new(),
            hashed_exprs_map: HashMap::new(),
            count_map: HashMap::new(),
            config: Config::default(),
        }
    }

    fn hash_recursive(&mut self, expr: &Expr<F, V, ()>) -> Vec<Expr<F, V, HashResult>> {
        let mut hashed_exprs = Vec::new();
        self.hash_and_collect(expr, &mut hashed_exprs);
        hashed_exprs
    }

    fn hash_and_collect(
        &mut self,
        expr: &Expr<F, V, ()>,
        hashed_exprs: &mut Vec<Expr<F, V, HashResult>>,
    ) {
        let hashed_expr = expr.hash(&self.random_assignments);

        if !matches!(expr, Expr::Const(_, _) | Expr::Query(_, _)) {
            let hash = hashed_expr.meta().hash;
            self.hashed_exprs_map
                .entry(hash)
                .or_insert_with(|| hashed_expr.clone());
        }

        hashed_exprs.push(hashed_expr.clone());

        if expr.degree() >= self.config.min_degree.unwrap_or(2) {
            match expr {
                Expr::Sum(ses, _) | Expr::Mul(ses, _) => {
                    for se in ses {
                        self.hash_and_collect(se, hashed_exprs);
                    }
                }
                Expr::Neg(se, _) | Expr::Pow(se, _, _) | Expr::MI(se, _) => {
                    self.hash_and_collect(se, hashed_exprs);
                }
                _ => {}
            }
        }
    }

    fn count_expression_occurrences(&mut self, hashed_exprs: &[Expr<F, V, HashResult>]) {
        for hashed_expr in hashed_exprs {
            let hash = hashed_expr.meta().hash;
            *self.count_map.entry(hash).or_insert(0) += 1;
        }
    }

    fn collect_common_expressions(&mut self) {
        self.common_exprs = self
            .hashed_exprs_map
            .iter()
            .filter_map(|(&hash, expr)| {
                self.count_map
                    .get(&hash)
                    .filter(|&&count| count >= self.config.min_occurrences.unwrap_or(2) as u32)
                    .map(|_| expr.clone())
            })
            .collect();
    }
}

// Basic signal factory.
#[derive(Default)]
struct SignalFactory<F> {
    count: u64,
    _p: PhantomData<F>,
}

impl<F> poly::SignalFactory<Queriable<F>> for SignalFactory<F> {
    fn create<S: Into<String>>(&mut self, annotation: S) -> Queriable<F> {
        self.count += 1;
        Queriable::Internal(InternalSignal::new(format!(
            "{}-{}",
            annotation.into(),
            self.count
        )))
    }
}

#[cfg(test)]
mod test {

}
