use crate::{
    field::Field,
    poly::{self, cse::replace_expr, Expr, HashResult, VarAssignments},
    sbpir::{query::Queriable, InternalSignal, StepType, SBPIR},
    wit_gen::NullTraceGenerator,
};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

pub(super) fn cse<F: Field + Hash>(
    mut circuit: SBPIR<F, NullTraceGenerator>,
) -> SBPIR<F, NullTraceGenerator> {
    // Create dummy assignments
    let mut queriables: Vec<Queriable<F>> = Vec::new();
    for signal in circuit.forward_signals.iter() {
        queriables.push(Queriable::Forward(*signal, false));
        queriables.push(Queriable::Forward(*signal, true));
    }

    // For each step type run a CSE pass
    for (_, step_type) in circuit.step_types.iter_mut() {
        let mut cse = CommonSubexpressionEliminator::new();
        cse.run(step_type, &mut queriables);
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

struct CommonSubexpressionEliminator<F> {
    common_exprs: Vec<Expr<F, Queriable<F>, HashResult>>,

    hashed_exprs_map: HashMap<u64, Expr<F, Queriable<F>, HashResult>>,
    count_map: HashMap<u64, u32>,

    config: Config,
}

impl<F: Field + Hash> CommonSubexpressionEliminator<F> {
    pub(super) fn run(&mut self, step: &mut StepType<F, ()>, queriables: &mut Vec<Queriable<F>>) {
        // Collect internal queriables from the step type and add them to the list of queriables
        step.signals.iter().for_each(|signal| {
            queriables.push(Queriable::Internal(*signal));
        });

        // Generate random assignments for the queriables
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let random_assignments: VarAssignments<F, Queriable<F>> = queriables
            .iter()
            .cloned()
            .map(|q| (q, F::random(&mut rng)))
            .collect();

        // Convert StepType<F, ()> to StepType<F, HashResult>
        let mut hashed_step = step.with_meta::<HashResult>(&random_assignments);

        // Collect and analyze all subexpressions
        self.collect_all_subexpressions(&hashed_step);
        self.identify_common_subexpressions();

        let mut signal_factory = SignalFactory::default();
        hashed_step
            .decomp_constraints(|expr| replace_expr(expr, &self.common_exprs, &mut signal_factory));

        // Convert back to StepType<F, ()> and update the original step
        *step = hashed_step.without_meta();
    }

    fn new() -> Self {
        CommonSubexpressionEliminator {
            common_exprs: Vec::new(),
            hashed_exprs_map: HashMap::new(),
            count_map: HashMap::new(),
            config: Config::default(),
        }
    }

    fn collect_all_subexpressions(&mut self, step: &StepType<F, HashResult>) {
        let mut all_subexpressions = Vec::new();

        // Collect subexpressions from constraints
        for constraint in &step.constraints {
            Self::collect_subexpressions(&constraint.expr, &mut all_subexpressions);
        }

        // Collect subexpressions from transition constraints
        for constraint in &step.transition_constraints {
            Self::collect_subexpressions(&constraint.expr, &mut all_subexpressions);
        }

        // Count occurrences of each subexpression
        for expr in all_subexpressions {
            let hash = expr.meta().hash;
            *self.count_map.entry(hash).or_insert(0) += 1;
            self.hashed_exprs_map.entry(hash).or_insert(expr);
        }
    }

    fn collect_subexpressions(
        expr: &Expr<F, Queriable<F>, HashResult>,
        subexpressions: &mut Vec<Expr<F, Queriable<F>, HashResult>>,
    ) {
        // Add the current expression to the list of subexpressions
        subexpressions.push(expr.clone());

        // Recursively collect subexpressions
        match expr {
            Expr::Sum(ses, _) | Expr::Mul(ses, _) => {
                for se in ses {
                    Self::collect_subexpressions(se, subexpressions);
                }
            }
            Expr::Neg(se, _) | Expr::Pow(se, _, _) | Expr::MI(se, _) => {
                Self::collect_subexpressions(se, subexpressions);
            }
            Expr::Const(_, _) | Expr::Query(_, _) | Expr::Halo2Expr(_, _) => {
                // These are leaf nodes, so we don't need to collect subexpressions
            }
        }
    }

    fn identify_common_subexpressions(&mut self) {
        self.common_exprs = self
            .hashed_exprs_map
            .iter()
            .filter_map(|(&hash, expr)| {
                if self.count_map.get(&hash).copied().unwrap_or(0)
                    >= self.config.min_occurrences.unwrap_or(2) as u32
                    && expr.degree() >= self.config.min_degree.unwrap_or(2)
                    && !matches!(expr, Expr::MI(_, _))
                // Exclude MI expressions
                {
                    Some(expr.clone())
                } else {
                    None
                }
            })
            .collect();
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
mod test {}
