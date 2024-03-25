use crate::{
    field::Field,
    pil::ir::powdr_pil::{PILCircuit, PILLookup},
    poly::Expr,
    sbpir::{query::Queriable, SBPIR},
    util::{uuid, UUID},
    wit_gen::TraceWitness,
};
use std::{collections::HashMap, fmt::Debug, hash::Hash};
extern crate regex;

pub fn compile<F: Clone + Debug + Field, TraceArgs>(
    ast: &SBPIR<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
    circuit_name: String,
    super_circuit_annotations_map: &Option<&HashMap<UUID, String>>,
) -> PILCircuit<F> {
    let col_witness = collect_witness_columns(ast);

    // HashMap of fixed column to fixed assignments
    let mut col_fixed = HashMap::new();

    if let Some(fixed_assignments) = &ast.fixed_assignments {
        fixed_assignments
            .iter()
            .for_each(|(queriable, assignments)| {
                let uuid = queriable.uuid();
                col_fixed.insert(
                    PILColumn::Fixed(
                        uuid,
                        clean_annotation(ast.annotations.get(&uuid).unwrap().clone()),
                    ),
                    assignments.clone(),
                );
            });
    }

    // Get last step instance UUID, so that we can disable transition of that instance
    let mut last_step_instance = 0;

    // Insert into col_fixed the map from step type fixed column to vector of {0,1} where 1 means
    // the step type is instantiated whereas 0 not. Each vector should have the same length as the
    // number of steps.
    if !ast.step_types.is_empty() && witness.is_some() {
        let step_instances = witness.as_ref().unwrap().step_instances.iter();

        // Get last step instance, so that we can disable transition of that instance
        last_step_instance = step_instances.clone().last().unwrap().step_type_uuid;

        for step_type in ast.step_types.values() {
            let step_type_instantiation: Vec<F> = step_instances
                .clone()
                .map(|step_instance| {
                    if step_instance.step_type_uuid == step_type.uuid() {
                        F::ONE
                    } else {
                        F::ZERO
                    }
                })
                .collect();
            assert_eq!(step_type_instantiation.len(), ast.num_steps);
            let uuid = step_type.uuid();
            col_fixed.insert(
                PILColumn::Fixed(
                    uuid,
                    clean_annotation(ast.annotations.get(&uuid).unwrap().clone()),
                ),
                step_type_instantiation,
            );
        }
    }

    // Create new UUID for ISFIRST and ISLAST. These are fixed columns unique to PIL.
    let is_first_uuid = uuid();
    let is_last_uuid = uuid();

    // ISFIRST and ISLAST are only relevant when there's non zero number of step instances.
    let num_step_instances = witness
        .as_ref()
        .map(|w| w.step_instances.len())
        .unwrap_or(0);
    if num_step_instances != 0 {
        // 1 for first row and 0 for all other rows; number of rows equals to number of steps
        let is_first_assignments = vec![F::ONE]
            .into_iter()
            .chain(std::iter::repeat(F::ZERO))
            .take(ast.num_steps)
            .collect();
        col_fixed.insert(
            PILColumn::Fixed(is_first_uuid, String::from("ISFIRST")),
            is_first_assignments,
        );

        // 0 for all rows except the last row, which is 1; number of rows equals to number of steps
        let is_last_assignments = std::iter::repeat(F::ZERO)
            .take(ast.num_steps - 1)
            .chain(std::iter::once(F::ONE))
            .collect();
        col_fixed.insert(
            PILColumn::Fixed(is_last_uuid, String::from("ISLAST")),
            is_last_assignments,
        );
    }

    // Compile step type elements, i.e. constraints, transitions, and lookups.
    let (mut constraints, lookups) = compile_steps(
        ast,
        last_step_instance,
        is_last_uuid,
        super_circuit_annotations_map,
    );

    // Insert pragma_first_step and pragma_last_step as constraints
    if let Some(first_step) = ast.first_step {
        // is_first * (1 - first_step) = 0
        constraints.push(PILExpr::Mul(vec![
            PILExpr::Query((
                PILColumn::Fixed(is_first_uuid, String::from("ISFIRST")),
                false,
            )),
            PILExpr::Sum(vec![
                PILExpr::Const(F::ONE),
                PILExpr::Neg(Box::new(PILExpr::Query((
                    PILColumn::Fixed(
                        first_step,
                        clean_annotation(ast.annotations.get(&first_step).unwrap().clone()),
                    ),
                    false,
                )))),
            ]),
        ]));
    }

    if let Some(last_step) = ast.last_step {
        // is_last * (1 - last_step) = 0
        constraints.push(PILExpr::Mul(vec![
            PILExpr::Query((
                PILColumn::Fixed(is_last_uuid, String::from("ISLAST")),
                false,
            )),
            PILExpr::Sum(vec![
                PILExpr::Const(F::ONE),
                PILExpr::Neg(Box::new(PILExpr::Query((
                    PILColumn::Fixed(
                        last_step,
                        clean_annotation(ast.annotations.get(&last_step).unwrap().clone()),
                    ),
                    false,
                )))),
            ]),
        ]));
    }

    PILCircuit {
        circuit_name,
        num_steps: ast.num_steps,
        col_witness,
        col_fixed,
        constraints,
        lookups,
    }
}

pub fn compile_super_circuits<F: Clone + Debug + Field, TraceArgs>(
    super_asts: Vec<SBPIR<F, TraceArgs>>,
    super_trace_witnesses: HashMap<UUID, TraceWitness<F>>,
    ast_id_to_ir_id_mapping: HashMap<UUID, UUID>,
    circuit_names: Vec<String>,
) -> Vec<PILCircuit<F>> {
    assert!(super_asts.len() == circuit_names.len());

    // Get annotations map for the super circuit, which is a HashMap of object UUID to object
    // annotation.
    let mut super_circuit_annotations_map: HashMap<UUID, String> = HashMap::new();

    // Loop over each AST.
    for (ast, circuit_name) in super_asts.iter().zip(circuit_names.iter()) {
        // Create `annotations_map` for each AST, to be added to `super_circuit_annotations_map`.
        let mut annotations_map: HashMap<UUID, String> = HashMap::new();

        // First, get AST level annotations.
        annotations_map.extend(ast.annotations.clone());

        // Second, get step level annotations.
        for step_type in ast.step_types.values() {
            annotations_map.extend(step_type.annotations.clone());
        }

        // Convert annotation to circuit_name.annotation, because this is the general format of
        // referring to variables in PIL if there are more than one circuit.
        super_circuit_annotations_map.extend(annotations_map.into_iter().map(
            |(uuid, annotation)| {
                (
                    uuid,
                    format!("{}.{}", circuit_name.clone(), clean_annotation(annotation)),
                )
            },
        ));

        // Finally, get annotations for the circuit names.
        super_circuit_annotations_map.insert(ast.id, circuit_name.clone());
    }

    // For each AST, find its corresponding TraceWitness. Note that some AST might not have a
    // corresponding TraceWitness, so witness is an Option.
    let mut pil_irs = Vec::new();
    for (ast, circuit_name) in super_asts.iter().zip(circuit_names.iter()) {
        let witness = super_trace_witnesses.get(ast_id_to_ir_id_mapping.get(&ast.id).unwrap());

        // Create PIL IR
        let pil_ir = compile(
            ast,
            witness.cloned(),
            circuit_name.clone(),
            &Some(&super_circuit_annotations_map),
        );

        pil_irs.push(pil_ir);
    }

    pil_irs
}

fn collect_witness_columns<F, TraceArgs>(ast: &SBPIR<F, TraceArgs>) -> Vec<PILColumn> {
    let mut col_witness = Vec::new();

    // Collect internal signals to witness columns.
    col_witness.extend(
        ast.step_types
            .values()
            .flat_map(|step_type| {
                step_type
                    .signals
                    .iter()
                    .map(|signal| {
                        PILColumn::Advice(signal.uuid(), clean_annotation(signal.annotation()))
                    })
                    .collect::<Vec<PILColumn>>()
            })
            .collect::<Vec<PILColumn>>(),
    );

    // Collect forward signals to witness columns.
    col_witness.extend(
        ast.forward_signals
            .iter()
            .map(|forward_signal| {
                PILColumn::Advice(
                    forward_signal.uuid(),
                    clean_annotation(forward_signal.annotation()),
                )
            })
            .collect::<Vec<PILColumn>>(),
    );

    // Collect shared signals to witness columns.
    col_witness.extend(
        ast.shared_signals
            .iter()
            .map(|shared_signal| {
                PILColumn::Advice(
                    shared_signal.uuid(),
                    clean_annotation(shared_signal.annotation()),
                )
            })
            .collect::<Vec<PILColumn>>(),
    );

    col_witness
}

fn compile_steps<F: Clone + Field, TraceArgs>(
    ast: &SBPIR<F, TraceArgs>,
    last_step_instance: UUID,
    is_last_uuid: UUID,
    super_circuit_annotations_map: &Option<&HashMap<UUID, String>>,
) -> (Vec<PILExpr<F, PILQuery>>, Vec<PILLookup>) {
    // transitions and constraints all become constraints in PIL
    let mut constraints = Vec::new();
    let mut lookups = Vec::new();

    if !ast.step_types.is_empty() {
        ast.step_types.values().for_each(|step_type| {
            // Create constraint statements.
            constraints.extend(
                step_type
                    .constraints
                    .iter()
                    .map(|constraint| {
                        PILExpr::Mul(vec![
                            PILExpr::Query((
                                PILColumn::Fixed(
                                    step_type.uuid(),
                                    clean_annotation(step_type.name()),
                                ),
                                false,
                            )),
                            chiquito_expr_to_pil_expr(
                                constraint.expr.clone(),
                                super_circuit_annotations_map,
                            ),
                        ])
                    })
                    .collect::<Vec<PILExpr<F, PILQuery>>>(),
            );

            // There's no distinction between constraint and transition in PIL
            // However, we do need to identify constraints with rotation in the last row
            // and disable them
            constraints.extend(
                step_type
                    .transition_constraints
                    .iter()
                    .map(|transition| {
                        let res = PILExpr::Mul(vec![
                            PILExpr::Query((
                                PILColumn::Fixed(
                                    step_type.uuid(),
                                    clean_annotation(step_type.name()),
                                ),
                                false,
                            )),
                            chiquito_expr_to_pil_expr(
                                transition.expr.clone(),
                                super_circuit_annotations_map,
                            ),
                        ]);
                        if step_type.uuid() == last_step_instance {
                            PILExpr::Mul(vec![
                                PILExpr::Sum(vec![
                                    PILExpr::Const(F::ONE),
                                    PILExpr::Neg(Box::new(PILExpr::Query((
                                        PILColumn::Fixed(is_last_uuid, String::from("ISLAST")),
                                        false,
                                    )))),
                                ]),
                                res,
                            ])
                        } else {
                            res
                        }
                    })
                    .collect::<Vec<PILExpr<F, PILQuery>>>(),
            );

            lookups.extend(
                step_type
                    .lookups
                    .iter()
                    .map(|lookup| {
                        (
                            PILColumn::Fixed(step_type.uuid(), clean_annotation(step_type.name())),
                            lookup
                                .exprs
                                .iter()
                                .map(|(lhs, rhs)| {
                                    (
                                        chiquito_lookup_column_to_pil_column(
                                            lhs.expr.clone(),
                                            super_circuit_annotations_map,
                                        ),
                                        chiquito_lookup_column_to_pil_column(
                                            rhs.clone(),
                                            super_circuit_annotations_map,
                                        ),
                                    )
                                })
                                .collect::<Vec<(PILColumn, PILColumn)>>(),
                        )
                    })
                    .collect::<Vec<PILLookup>>(),
            );
        });
    }

    (constraints, lookups)
}

// Convert lookup columns (src and dest) in Chiquito to PIL column. Note that Chiquito lookup
// columns have to be Expr::Query type.
fn chiquito_lookup_column_to_pil_column<F>(
    src: Expr<F, Queriable<F>>,
    super_circuit_annotations_map: &Option<&HashMap<UUID, String>>,
) -> PILColumn {
    match src {
        Expr::Query(queriable) => {
            chiquito_queriable_to_pil_query(queriable, super_circuit_annotations_map).0
        }
        _ => panic!("Lookup source is not queriable."),
    }
}

// PIL expression and constraint
#[derive(Clone)]
pub enum PILExpr<F, PILQuery> {
    Const(F),
    Sum(Vec<PILExpr<F, PILQuery>>),
    Mul(Vec<PILExpr<F, PILQuery>>),
    Neg(Box<PILExpr<F, PILQuery>>),
    Pow(Box<PILExpr<F, PILQuery>>, u32),
    Query(PILQuery),
}

fn chiquito_expr_to_pil_expr<F: Clone>(
    expr: Expr<F, Queriable<F>>,
    super_circuit_annotations_map: &Option<&HashMap<UUID, String>>,
) -> PILExpr<F, PILQuery> {
    match expr {
        Expr::Const(constant) => PILExpr::Const(constant),
        Expr::Sum(sum) => {
            let mut pil_sum = Vec::new();
            for expr in sum {
                pil_sum.push(chiquito_expr_to_pil_expr(
                    expr,
                    super_circuit_annotations_map,
                ));
            }
            PILExpr::Sum(pil_sum)
        }
        Expr::Mul(mul) => {
            let mut pil_mul = Vec::new();
            for expr in mul {
                pil_mul.push(chiquito_expr_to_pil_expr(
                    expr,
                    super_circuit_annotations_map,
                ));
            }
            PILExpr::Mul(pil_mul)
        }
        Expr::Neg(neg) => PILExpr::Neg(Box::new(chiquito_expr_to_pil_expr(
            *neg,
            super_circuit_annotations_map,
        ))),
        Expr::Pow(pow, power) => PILExpr::Pow(
            Box::new(chiquito_expr_to_pil_expr(
                *pow,
                super_circuit_annotations_map,
            )),
            power,
        ),
        Expr::Query(queriable) => PILExpr::Query(chiquito_queriable_to_pil_query(
            queriable,
            super_circuit_annotations_map,
        )),
        Expr::Halo2Expr(_) => {
            panic!("Halo2 native expression not supported by PIL backend.")
        }
        Expr::MI(_) => {
            panic!("MI not supported by PIL backend.")
        }
    }
}

pub type PILQuery = (PILColumn, bool); // column, rotation

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PILColumn {
    Advice(UUID, String), // UUID, annotation
    Fixed(UUID, String),
}

impl PILColumn {
    pub fn uuid(&self) -> UUID {
        match self {
            PILColumn::Advice(uuid, _) => *uuid,
            PILColumn::Fixed(uuid, _) => *uuid,
        }
    }

    pub fn annotation(&self) -> String {
        match self {
            PILColumn::Advice(_, annotation) => annotation.clone(),
            PILColumn::Fixed(_, annotation) => annotation.clone(),
        }
    }
}

pub fn clean_annotation(annotation: String) -> String {
    annotation.replace(' ', "_")
}

// Convert queriable to PIL column recursively. Major differences are: 1. PIL doesn't distinguish
// internal, forward, or shared columns as they are all advice; 2. PIL only supports the next
// rotation, so there's no previous or arbitrary rotation.
fn chiquito_queriable_to_pil_query<F>(
    query: Queriable<F>,
    super_circuit_annotations_map: &Option<&HashMap<UUID, String>>,
) -> PILQuery {
    match query {
        Queriable::Internal(s) => {
            if super_circuit_annotations_map.is_none() {
                (
                    PILColumn::Advice(s.uuid(), clean_annotation(s.annotation())),
                    false,
                )
            } else {
                let annotation = super_circuit_annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&s.uuid())
                    .unwrap();
                (
                    PILColumn::Advice(s.uuid(), clean_annotation(annotation.clone())),
                    false,
                )
            }
        }
        Queriable::Forward(s, rot) => {
            if super_circuit_annotations_map.is_none() {
                (
                    PILColumn::Advice(s.uuid(), clean_annotation(s.annotation())),
                    rot,
                )
            } else {
                let annotation = super_circuit_annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&s.uuid())
                    .unwrap();
                (
                    PILColumn::Advice(s.uuid(), clean_annotation(annotation.clone())),
                    rot,
                )
            }
        }
        Queriable::Shared(s, rot) => {
            let annotation = if super_circuit_annotations_map.is_none() {
                clean_annotation(s.annotation())
            } else {
                super_circuit_annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&s.uuid())
                    .unwrap()
                    .clone()
            };
            if rot == 0 {
                (PILColumn::Advice(s.uuid(), annotation), false)
            } else if rot == 1 {
                (PILColumn::Advice(s.uuid(), annotation), true)
            } else {
                panic!(
                    "PIL backend does not support shared signal with rotation other than 0 or 1."
                )
            }
        }
        Queriable::Fixed(s, rot) => {
            let annotation = if super_circuit_annotations_map.is_none() {
                clean_annotation(s.annotation())
            } else {
                super_circuit_annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&s.uuid())
                    .unwrap()
                    .clone()
            };
            if rot == 0 {
                (PILColumn::Fixed(s.uuid(), annotation), false)
            } else if rot == 1 {
                (PILColumn::Fixed(s.uuid(), annotation), true)
            } else {
                panic!("PIL backend does not support fixed signal with rotation other than 0 or 1.")
            }
        }
        Queriable::StepTypeNext(s) => (
            PILColumn::Fixed(s.uuid(), clean_annotation(s.annotation())),
            true,
        ),
        Queriable::Halo2AdviceQuery(_, _) => {
            panic!("Halo2 native advice query not supported by PIL backend.")
        }
        Queriable::Halo2FixedQuery(_, _) => {
            panic!("Halo2 native fixed query not supported by PIL backend.")
        }
        Queriable::_unaccessible(_) => todo!(),
    }
}
