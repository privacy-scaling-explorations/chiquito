use crate::{
    ast::{query::Queriable, Circuit},
    pil::ir::powdr_pil::{PilCircuit, PilLookup},
    poly::Expr,
    util::UUID,
    wit_gen::TraceWitness,
};
use std::{collections::HashMap, fmt::Debug};
extern crate regex;

pub fn compile<F: Clone + Debug, TraceArgs>(
    ast: Circuit<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
    circuit_name: String,
) -> PilCircuit<F> {
    // Create a Vec<UUID> for witness columns in PIL, corresponding to internal signals, forward
    // signals, and shared signals in Chiquito. This vector will be used later for
    // witness column declaration in PIL.
    let col_witness = collect_witness_columns(&ast);

    // Create HashMap of fixed signal UUID to vector of fixed assignments.
    let mut fixed_signals = HashMap::new();

    if let Some(fixed_assignments) = &ast.fixed_assignments {
        fixed_assignments
            .iter()
            .for_each(|(queriable, assignments)| {
                fixed_signals.insert(queriable.uuid(), assignments.clone());
            });
    }

    // Create HashMap of step type UUID to vector of {0, 1} where 1 means the step type is
    // instantiated whereas 0 not. Each vector should have the same length as the number of
    // steps.
    let step_types_instantiations = collect_step_instances(&ast, &witness);

    // Compile step type elements, i.e. constraints, transitions, and lookups.
    let (constraints, transitions, lookups) = compile_steps(&ast);

    PilCircuit {
        circuit_name,
        num_steps: ast.num_steps,

        col_witness,

        fixed_signals,
        step_types_instantiations,
        first_step: ast.first_step,
        last_step: ast.last_step,

        step_types: ast.step_types.keys().cloned().collect(), /* returns empty if
                                                               * `step_types` is empty
                                                               * HashMap */
        constraints,
        transitions,
        lookups,
    }
}

fn collect_witness_columns<F, TraceArgs>(ast: &Circuit<F, TraceArgs>) -> Vec<UUID> {
    let mut col_witness = Vec::new();

    // Collect UUIDs of internal signals stored at the step type level. These internal signals
    // are not dedupped, meaning that some of them might have different UUIDs across different
    // step types but are have the same annotation and are the same signal. Internal signals
    // with the same annotation in the same circuit will be dedupped when converting PilCircuit
    // to PIL code.
    col_witness.extend(
        ast.step_types
            .values()
            .flat_map(|step_type| {
                step_type
                    .signals
                    .iter()
                    .map(|signal| signal.uuid())
                    .collect::<Vec<UUID>>()
            })
            .collect::<Vec<UUID>>(),
    );

    // Collect UUIDs of forward signals stored at the circuit level.
    col_witness.extend(
        ast.forward_signals
            .iter()
            .map(|forward_signal| forward_signal.uuid())
            .collect::<Vec<UUID>>(),
    );

    // Collect UUIDs of shared signals stored at the circuit level.
    col_witness.extend(
        ast.shared_signals
            .iter()
            .map(|shared_signal| shared_signal.uuid())
            .collect::<Vec<UUID>>(),
    );

    col_witness
}

fn collect_step_instances<F, TraceArgs>(
    ast: &Circuit<F, TraceArgs>,
    witness: &Option<TraceWitness<F>>,
) -> HashMap<UUID, Vec<usize>> {
    let mut step_types_instantiations = HashMap::new();

    if !ast.step_types.is_empty() && witness.is_some() {
        let step_instances = witness.as_ref().unwrap().step_instances.iter();

        for step_type in ast.step_types.values() {
            let step_type_instantiation: Vec<usize> = step_instances
                .clone()
                .map(|step_instance| {
                    if step_instance.step_type_uuid == step_type.uuid() {
                        1
                    } else {
                        0
                    }
                })
                .collect();
            assert_eq!(step_type_instantiation.len(), ast.num_steps);
            step_types_instantiations.insert(step_type.uuid(), step_type_instantiation);
        }
    }

    step_types_instantiations
}

type ConstraintsByStepID<F> = HashMap<UUID, Vec<Expr<F, Queriable<F>>>>;
type TransitionsByStepID<F> = HashMap<UUID, Vec<Expr<F, Queriable<F>>>>;
type LookupsByStepID<F> = HashMap<UUID, Vec<PilLookup<F>>>;

fn compile_steps<F: Clone, TraceArgs>(
    ast: &Circuit<F, TraceArgs>,
) -> (
    ConstraintsByStepID<F>,
    TransitionsByStepID<F>,
    LookupsByStepID<F>,
) {
    // Group constraints, transitions, and lookups by step type UUID using HashMaps.
    let mut constraints = HashMap::new();
    let mut transitions = HashMap::new();
    let mut lookups = HashMap::new();

    if !ast.step_types.is_empty() {
        ast.step_types.values().for_each(|step_type| {
            // Create constraint statements.
            constraints.insert(
                step_type.uuid(),
                step_type
                    .constraints
                    .iter()
                    .map(|constraint| constraint.expr.clone())
                    .collect::<Vec<Expr<F, Queriable<F>>>>(),
            );

            transitions.insert(
                step_type.uuid(),
                step_type
                    .transition_constraints
                    .iter()
                    .map(|transition| transition.expr.clone())
                    .collect::<Vec<Expr<F, Queriable<F>>>>(),
            );

            // Note that there's no lookup table in PIL, so we only need to convert lookups.
            lookups.insert(
                step_type.uuid(),
                step_type
                    .lookups
                    .iter()
                    .map(|lookup| {
                        lookup
                            .exprs
                            .iter()
                            .map(|(lhs, rhs)| (lhs.expr.clone(), rhs.clone()))
                            .collect::<Vec<(Expr<F, Queriable<F>>, Expr<F, Queriable<F>>)>>()
                    })
                    .collect::<Vec<PilLookup<F>>>(),
            );
        });
    }

    (constraints, transitions, lookups)
}
