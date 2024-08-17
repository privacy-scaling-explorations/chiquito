use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    field::Field,
    poly::{
        self,
        cse::{create_common_ses_signal, replace_expr},
        Expr, HashResult, VarAssignments,
    },
    sbpir::{query::Queriable, ForwardSignal, InternalSignal, StepType, SBPIR},
    wit_gen::NullTraceGenerator,
};

#[derive(Clone, Debug)]
pub(super) struct CseConfig {
    max_iterations: usize,
}

impl Default for CseConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
        }
    }
}

#[allow(dead_code)]
pub fn config(max_iterations: Option<usize>) -> CseConfig {
    CseConfig {
        max_iterations: max_iterations.unwrap_or(100),
    }
}

pub(super) trait Scoring<F: Field + Hash> {
    fn score(&self, expr: &Expr<F, Queriable<F>, HashResult>, info: &SubexprInfo) -> usize;
}

pub(super) struct Scorer {
    min_degree: usize,
    min_occurrences: usize,
}

impl Default for Scorer {
    fn default() -> Self {
        Self {
            min_degree: 2,
            min_occurrences: 2,
        }
    }
}

impl<F: Field + Hash> Scoring<F> for Scorer {
    fn score(&self, _expr: &Expr<F, Queriable<F>, HashResult>, info: &SubexprInfo) -> usize {
        if info.degree < self.min_degree || info.count < self.min_occurrences {
            0
        } else {
            info.count * info.degree
        }
    }
}

/// Common Subexpression Elimination (CSE) optimization.
/// This optimization replaces common subexpressions with new internal signals for the step type.
/// This is done by each time finding the optimal subexpression to replace and creating a new signal
/// for it and replacing it in all constraints.
/// The process is repeated until no more common subexpressions are found.
/// Equivalent expressions are found by hashing the expressions with random assignments to the
/// queriables. Using the Schwartz-Zippel lemma, we can determine if two expressions are equivalent
/// with high probability.
#[allow(dead_code)]
pub(super) fn cse<F: Field + Hash, S: Scoring<F>>(
    mut circuit: SBPIR<F, NullTraceGenerator>,
    config: CseConfig,
    scorer: &S,
) -> SBPIR<F, NullTraceGenerator> {
    for (_, machine) in circuit.machines.iter_mut() {
        for (_, step_type) in machine.step_types.iter_mut() {
            cse_for_step(step_type, &machine.forward_signals, &config, scorer)
        }
    }
    circuit
}

fn cse_for_step<F: Field + Hash, S: Scoring<F>>(
    step_type: &mut StepType<F, ()>,
    forward_signals: &[ForwardSignal],
    config: &CseConfig,
    scorer: &S,
) {
    let mut signal_factory = SignalFactory::default();
    let mut replaced_hashes = HashSet::new();

    for _ in 0..config.max_iterations {
        let mut queriables = Vec::<Queriable<F>>::new();

        forward_signals.iter().for_each(|signal| {
            queriables.push(Queriable::Forward(*signal, false));
            queriables.push(Queriable::Forward(*signal, true));
        });
        step_type.signals.iter().for_each(|signal| {
            queriables.push(Queriable::Internal(*signal));
        });

        // Generate random assignments for the queriables
        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let random_assignments: VarAssignments<F, Queriable<F>> = queriables
            .iter()
            .cloned()
            .map(|q| (q, F::random(&mut rng)))
            .collect();

        // Turn all Expr<F, V, ()> into Expr<F, V, HashResult>
        let mut step_type_with_hash = step_type.transform_meta(|expr| {
            let hashed_expr = expr.hash(&random_assignments);
            hashed_expr.meta().clone()
        });

        // Extract all the expressions from the step type
        let mut exprs = Vec::<Expr<F, Queriable<F>, HashResult>>::new();

        for constraint in &step_type_with_hash.constraints {
            exprs.push(constraint.expr.clone());
        }

        // Find the optimal subexpression to replace
        if let Some(common_expr) = find_optimal_subexpression(&exprs, &replaced_hashes, scorer) {
            // Add the hash of the replaced expression to the set
            replaced_hashes.insert(common_expr.meta().hash);
            // Create a new signal for the common subexpression
            let (common_se, decomp) = create_common_ses_signal(&common_expr, &mut signal_factory);

            // Add the new signal to the step type and a constraint for it
            decomp.auto_signals.iter().for_each(|(q, expr)| {
                if let Queriable::Internal(signal) = q {
                    step_type_with_hash.add_internal(*signal);
                }
                step_type_with_hash.auto_signals.insert(*q, expr.clone());
                step_type_with_hash.add_constr(format!("{:?}", q), expr.clone());
            });
            decomp.constrs.iter().for_each(|expr| {
                step_type_with_hash.add_constr(format!("{:?}", expr), expr.clone());
            });

            // Replace the common subexpression in all constraints
            step_type_with_hash
                .constraints
                .iter_mut()
                .for_each(|constraint| {
                    constraint.expr = replace_expr(&constraint.expr, &common_se);
                });
        } else {
            // No more common subexpressions found, exit the loop
            break;
        }
        *step_type = step_type_with_hash.transform_meta(|_| ());
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct SubexprInfo {
    count: usize,
    degree: usize,
}

/// Information about a subexpression to help find the optimal subexpression to replace.
impl SubexprInfo {
    fn new(count: usize, degree: usize) -> Self {
        Self { count, degree }
    }

    fn update(&mut self, degree: usize) {
        self.count += 1;
        self.degree = self.degree.max(degree);
    }
}

/// Find the optimal subexpression to replace in a list of expressions.
fn find_optimal_subexpression<F: Field + Hash, S: Scoring<F>>(
    exprs: &[Expr<F, Queriable<F>, HashResult>],
    replaced_hashes: &HashSet<u64>,
    scorer: &S,
) -> Option<Expr<F, Queriable<F>, HashResult>> {
    let mut count_map = HashMap::<u64, SubexprInfo>::new();
    let mut hash_to_expr = HashMap::<u64, Expr<F, Queriable<F>, HashResult>>::new();

    // Extract all subexpressions and count them
    for expr in exprs.iter() {
        count_subexpressions(expr, &mut count_map, &mut hash_to_expr, replaced_hashes);
    }

    // Find the best common subexpression to replace based on the score
    let best_subexpr = count_map
        .iter()
        .map(|(&hash, info)| {
            let expr = hash_to_expr.get(&hash).unwrap();
            let score = scorer.score(expr, info);
            (hash, score)
        })
        .filter(|&(_, score)| score > 0)
        .max_by_key(|&(_, score)| score)
        .map(|(hash, _)| hash);

    best_subexpr.and_then(|hash| hash_to_expr.get(&hash).cloned())
}

/// Count the subexpressions in an expression and store them in a map.
fn count_subexpressions<F: Field + Hash>(
    expr: &Expr<F, Queriable<F>, HashResult>,
    count_map: &mut HashMap<u64, SubexprInfo>,
    hash_to_expr: &mut HashMap<u64, Expr<F, Queriable<F>, HashResult>>,
    replaced_hashes: &HashSet<u64>,
) {
    let degree = expr.degree();
    let hash_result = expr.meta().hash;

    // Only count and store if not already replaced
    if !replaced_hashes.contains(&hash_result) {
        // Store the expression with its hash
        hash_to_expr.insert(hash_result, expr.clone());

        count_map
            .entry(hash_result)
            .and_modify(|info| info.update(degree))
            .or_insert(SubexprInfo::new(1, degree));
    }

    // Recurse into subexpressions
    match expr {
        Expr::Const(_, _) | Expr::Query(_, _) => {}
        Expr::Sum(exprs, _) | Expr::Mul(exprs, _) => {
            for subexpr in exprs {
                count_subexpressions(subexpr, count_map, hash_to_expr, replaced_hashes);
            }
        }
        Expr::Neg(subexpr, _) | Expr::MI(subexpr, _) => {
            count_subexpressions(subexpr, count_map, hash_to_expr, replaced_hashes);
        }
        Expr::Pow(subexpr, _, _) => {
            count_subexpressions(subexpr, count_map, hash_to_expr, replaced_hashes);
        }
        _ => {}
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
    use std::collections::{HashMap, HashSet};

    use halo2_proofs::halo2curves::bn256::Fr;
    use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

    use crate::{
        compiler::cse::{cse, CseConfig, Scorer},
        field::Field,
        poly::{Expr, VarAssignments},
        sbpir::{query::Queriable, sbpir_machine::SBPIRMachine, InternalSignal, StepType, SBPIR},
        util::uuid,
        wit_gen::NullTraceGenerator,
    };

    use super::find_optimal_subexpression;

    #[test]
    fn test_find_optimal_subexpression() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b = Queriable::Internal(InternalSignal::new("b"));
        let c = Queriable::Internal(InternalSignal::new("c"));
        let d = Queriable::Internal(InternalSignal::new("d"));
        let e = Queriable::Internal(InternalSignal::new("e"));
        let f = Queriable::Internal(InternalSignal::new("f"));
        let vars = vec![a, b, c, d, e, f];

        let expr1 = a * b + c;
        let expr2 = c + b + a;
        let expr3 = e * f * d * a * b + c;
        let expr4 = e * f * d + c;
        let expr5 = expr1.clone() + e * f * d;
        let exprs = vec![expr1, expr2, expr3, expr4.clone(), expr5];

        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let mut rand_assignments = VarAssignments::new();
        for var in vars.iter() {
            rand_assignments.insert(*var, Fr::random(&mut rng));
        }

        let mut hashed_exprs = Vec::new();
        for expr in exprs.iter() {
            let hashed_expr = expr.hash(&rand_assignments);
            hashed_exprs.push(hashed_expr);
        }

        let scorer = Scorer::default();

        let best_expr = find_optimal_subexpression(&hashed_exprs, &HashSet::new(), &scorer);

        assert_eq!(format!("{:?}", best_expr.unwrap()), "(e * f * d)");
    }

    #[test]
    fn test_cse() {
        let a = InternalSignal::new("a");
        let b = InternalSignal::new("b");
        let c = InternalSignal::new("c");
        let d = InternalSignal::new("d");
        let e = InternalSignal::new("e");
        let f = InternalSignal::new("f");

        let expr1: Expr<Fr, Queriable<Fr>, ()> = Expr::Query(Queriable::Internal(a), ())
            * Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(c), ());
        let expr2 = Expr::Query(Queriable::Internal(c), ())
            + Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(a), ());
        let expr3: Expr<Fr, Queriable<Fr>, ()> = Expr::Const(Fr::from(4), ())
            + Expr::Query(Queriable::Internal(a), ()) * Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(c), ());
        let expr4 = Expr::Query(Queriable::Internal(e), ())
            * Expr::Query(Queriable::Internal(f), ())
            * Expr::Query(Queriable::Internal(d), ());
        let expr5 = expr1.clone() + expr4.clone();

        let mut step: StepType<Fr, ()> = StepType::new(uuid(), "example_step".to_string());

        step.add_internal(a);
        step.add_internal(b);
        step.add_internal(c);
        step.add_internal(d);
        step.add_internal(e);
        step.add_internal(f);

        step.add_constr("expr1".into(), expr1);
        step.add_constr("expr2".into(), expr2);
        step.add_constr("expr3".into(), expr3);
        step.add_constr("expr4".into(), expr4.clone());
        step.add_constr("expr5".into(), expr5);

        let mut machine: SBPIRMachine<Fr, NullTraceGenerator> = SBPIRMachine::default();
        let step_uuid = machine.add_step_type_def(step);
        let mut machines = HashMap::new();
        machines.insert(uuid(), machine);
        let circuit = SBPIR {
            machines,
            identifiers: HashMap::new(),
        };

        let scorer = Scorer::default();
        let circuit = cse(circuit, CseConfig::default(), &scorer);

        let machine = circuit.machines.iter().next().unwrap().1;
        let step = machine.step_types.get(&step_uuid).unwrap();

        // Check if CSE was applied
        assert!(
            step.auto_signals.len() > 0,
            "No common subexpressions were found"
        );

        // Helper function to check if an expression contains a CSE signal
        fn contains_cse_signal(expr: &Expr<Fr, Queriable<Fr>, ()>) -> bool {
            match expr {
                Expr::Query(Queriable::Internal(signal), _) => {
                    signal.annotation().starts_with("cse-")
                }
                Expr::Sum(exprs, _) | Expr::Mul(exprs, _) => exprs.iter().any(contains_cse_signal),
                Expr::Neg(sub_expr, _) => contains_cse_signal(sub_expr),
                _ => false,
            }
        }

        // Check if at least one constraint contains a CSE signal
        let has_cse_constraint = step
            .constraints
            .iter()
            .any(|constraint| contains_cse_signal(&constraint.expr));
        assert!(has_cse_constraint, "No constraints with CSE signals found");

        // Check for specific optimizations without relying on exact CSE signal names
        let has_optimized_efg = step
            .constraints
            .iter()
            .any(|constraint| match &constraint.expr {
                Expr::Sum(terms, _) => {
                    terms.iter().any(|term| match term {
                        Expr::Mul(factors, _) => {
                            factors.len() == 3
                                && factors
                                    .iter()
                                    .all(|f| matches!(f, Expr::Query(Queriable::Internal(_), _)))
                        }
                        _ => false,
                    }) && terms.iter().any(contains_cse_signal)
                }
                _ => false,
            });
        assert!(
            has_optimized_efg,
            "Expected optimization for (e * f * d) not found"
        );

        let has_optimized_ab = step
            .constraints
            .iter()
            .any(|constraint| match &constraint.expr {
                Expr::Sum(terms, _) => {
                    terms.iter().any(|term| match term {
                        Expr::Mul(factors, _) => {
                            factors.len() == 2
                                && factors
                                    .iter()
                                    .all(|f| matches!(f, Expr::Query(Queriable::Internal(_), _)))
                        }
                        _ => false,
                    }) && terms.iter().any(contains_cse_signal)
                }
                _ => false,
            });
        assert!(
            has_optimized_ab,
            "Expected optimization for (a * b) not found"
        );

        // Check if the common subexpressions were actually created
        let cse_signals: Vec<_> = step
            .auto_signals
            .values()
            .filter(|expr| matches!(expr, Expr::Mul(_, _)))
            .collect();

        assert!(
            cse_signals.len() >= 2,
            "Expected at least two multiplication CSEs"
        );

        let has_ab_cse = cse_signals.iter().any(|expr| {
            if let Expr::Mul(factors, _) = expr {
                factors.len() == 2
                    && factors
                        .iter()
                        .all(|f| matches!(f, Expr::Query(Queriable::Internal(_), _)))
            } else {
                false
            }
        });
        assert!(has_ab_cse, "CSE for (a * b) not found in auto_signals");

        let has_efg_cse = cse_signals.iter().any(|expr| {
            if let Expr::Mul(factors, _) = expr {
                factors.len() == 3
                    && factors
                        .iter()
                        .all(|f| matches!(f, Expr::Query(Queriable::Internal(_), _)))
            } else {
                false
            }
        });
        assert!(has_efg_cse, "CSE for (e * f * d) not found in auto_signals");
    }

    #[derive(Clone)]
    struct TestStruct {
        value: String,
    }

    #[test]
    fn test_step_type_transform_meta() {
        let a = InternalSignal::new("a");
        let b = InternalSignal::new("b");
        let c = InternalSignal::new("c");
        let d = InternalSignal::new("d");
        let e = InternalSignal::new("e");
        let f = InternalSignal::new("f");

        let expr1: Expr<Fr, Queriable<Fr>, ()> = Expr::Query(Queriable::Internal(a), ())
            * Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(c), ());
        let expr2 = Expr::Query(Queriable::Internal(c), ())
            + Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(a), ());
        let expr3: Expr<Fr, Queriable<Fr>, ()> = Expr::Const(Fr::from(4), ())
            + Expr::Query(Queriable::Internal(a), ()) * Expr::Query(Queriable::Internal(b), ())
            + Expr::Query(Queriable::Internal(c), ());
        let expr4 = Expr::Query(Queriable::Internal(e), ())
            * Expr::Query(Queriable::Internal(f), ())
            * Expr::Query(Queriable::Internal(d), ());
        let expr5 = expr1.clone() + expr4.clone();

        let mut step: StepType<Fr, ()> = StepType::new(uuid(), "example_step".to_string());

        step.add_internal(a);
        step.add_internal(b);
        step.add_internal(c);
        step.add_internal(d);
        step.add_internal(e);
        step.add_internal(f);

        step.add_constr("expr1".into(), expr1);
        step.add_constr("expr2".into(), expr2);
        step.add_constr("expr3".into(), expr3);
        step.add_constr("expr4".into(), expr4);
        step.add_constr("expr5".into(), expr5);

        let step_transform_meta = step.transform_meta(|expr| TestStruct {
            value: format!("Expr: {:?}", expr),
        });

        for constraint in &step_transform_meta.constraints {
            assert_eq!(
                constraint.expr.meta().value,
                format!("Expr: {:?}", constraint.expr)
            );
        }
    }
}
