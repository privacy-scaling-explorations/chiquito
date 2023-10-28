use crate::{
    ast::{query::Queriable, Circuit},
    field::Field,
    plonkish::ir::sc::SuperCircuit,
    poly::Expr,
    util::UUID,
    wit_gen::TraceWitness,
};
use std::{
    collections::HashMap,
    fmt::{Debug, Write},
};
extern crate regex;

// PIL circuit IR
pub struct PilCircuit<F> {
    // circuit level
    pub circuit_name: String,
    pub num_steps: usize,

    // circuit level - col witness
    pub col_witness: Vec<UUID>, // internal signal NOT dedupped

    // circuit level - col fixed
    pub fixed_signals: HashMap<UUID, Vec<F>>, // fixed signal UUID -> fixed assignments vector
    pub step_types_instantiations: HashMap<UUID, Vec<usize>>, /* step type UUID -> step
                                               * instances
                                               * vector {0, 1}^num_steps */
    pub first_step: Option<UUID>,
    pub last_step: Option<UUID>,

    // step type level
    pub step_types: Vec<UUID>,
    pub constraints: HashMap<UUID, Vec<Expr<F, Queriable<F>>>>, // step type UUID -> constraints
    pub transitions: HashMap<UUID, Vec<Expr<F, Queriable<F>>>>,
    pub lookups: HashMap<UUID, Vec<PilLookup<F>>>, // step type UUID -> lookups vector
}

type PilLookup<F> = Vec<(Expr<F, Queriable<F>>, Expr<F, Queriable<F>>)>;

impl<F: Clone + Debug> PilCircuit<F> {
    pub fn from_ast_and_witness<TraceArgs>(
        ast: Circuit<F, TraceArgs>,
        witness: Option<TraceWitness<F>>,
        circuit_name: String,
    ) -> PilCircuit<F> {
        // Create a Vec<UUID> for witness columns in PIL, corresponding to internal signals, forward
        // signals, and shared signals in Chiquito. This vector will be used later for
        // witness column declaration in PIL.
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

        // Group constraints, transitions, and lookups by step type UUID using HashMaps.
        let mut constraints: HashMap<UUID, Vec<Expr<F, Queriable<F>>>> = HashMap::new();
        let mut transitions: HashMap<UUID, Vec<Expr<F, Queriable<F>>>> = HashMap::new();

        let mut lookups: HashMap<UUID, Vec<PilLookup<F>>> = HashMap::new();

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

    // Generate PIL code given the IR of a single PIL circuit. Need to supply `annotations_map`,
    // which only need to contain annotations for the circuit's own components if we are converting
    // a standalone circuit. If we are converting a super circuit, `annotations_map` also needs to
    // contain annotations for components outside the circuit.
    pub fn generate_pil_given_annotations(
        self: &PilCircuit<F>,
        annotations_map: &HashMap<UUID, String>,
    ) -> String {
        let mut pil = String::new(); // The string to return.

        writeln!(
            pil,
            "// ===== START OF CIRCUIT: {} =====",
            self.circuit_name
        )
        .unwrap();

        // Namespace is equivalent to a circuit in PIL. Note that we default `circuit_name` to
        // "Circuit" unless supplied.
        writeln!(
            pil,
            "constant %NUM_STEPS_{} = {};",
            self.circuit_name.to_uppercase(),
            self.num_steps
        )
        .unwrap();
        writeln!(
            pil,
            "namespace {}(%NUM_STEPS_{});",
            self.circuit_name.to_uppercase(),
            self.circuit_name.to_uppercase()
        )
        .unwrap();

        // Declare witness columns in PIL.
        if !self.col_witness.is_empty() {
            writeln!(pil, "// === Witness Columns for Signals ===").unwrap();
            let mut col_witness = String::from("col witness ");

            let mut col_witness_vars = self
                .col_witness
                .iter()
                .map(|uuid| annotations_map.get(uuid).unwrap().clone())
                .collect::<Vec<String>>();

            // Get unique witness column annotations, because the same internal signal across
            // different step types have different UUIDs and therefore appear multiple times.
            col_witness_vars.sort();
            col_witness_vars.dedup();
            col_witness = col_witness + col_witness_vars.join(", ").as_str() + ";";
            writeln!(pil, "{}", col_witness).unwrap();
        }

        // Convert fixed signals and their assignments in Chiquito to fixed columns in PIL.
        if !self.fixed_signals.is_empty() {
            writeln!(pil, "// === Fixed Columns for Signals ===").unwrap();
            for (fixed_signal_id, assignments) in self.fixed_signals.iter() {
                let fixed_name = annotations_map.get(fixed_signal_id).unwrap().clone();
                let mut assignments_string = String::new();
                let assignments_vec = assignments
                    .iter()
                    .map(|assignment| format!("{:?}", assignment))
                    .collect::<Vec<String>>();
                write!(
                    assignments_string,
                    "{}",
                    assignments_vec.join(", ").as_str()
                )
                .unwrap();
                writeln!(pil, "col fixed {} = [{}];", fixed_name, assignments_string).unwrap();
            }
        }

        // Create a step selector fixed column in PIL for each step type.
        if !self.step_types_instantiations.is_empty() {
            writeln!(pil, "// === Fixed Columns for Step Type Selectors ===").unwrap();
            for (step_type_id, step_type_instantiation) in self.step_types_instantiations.iter() {
                let step_type_name = annotations_map.get(step_type_id).unwrap().clone();
                let mut step_type_selector = String::new();
                write!(step_type_selector, "col fixed {} = [", step_type_name).unwrap();

                for (index, step_instance) in step_type_instantiation.iter().enumerate() {
                    write!(step_type_selector, "{}", step_instance).unwrap();
                    if index == self.num_steps - 1 {
                        write!(step_type_selector, "]").unwrap();
                    } else {
                        write!(step_type_selector, ", ").unwrap();
                    }
                }
                writeln!(pil, "{}", step_type_selector).unwrap();
            }
        }

        // Create fixed columns ISFIRST and ISLAST needed for pragma_first_step and
        // pragma_last_step.
        writeln!(
            pil,
            "col fixed ISFIRST(i) {{ match i {{ 0 => 1, _ => 0 }} }};"
        )
        .unwrap();
        writeln!(
            pil,
            "col fixed ISLAST(i) {{ match i {{ %NUM_STEPS_{} - 1 => 1, _ => 0 }} }};",
            self.circuit_name.to_uppercase()
        )
        .unwrap();

        // Iterate over step types to create constraint statements and lookups.
        if !self.step_types.is_empty() {
            for step_type in &self.step_types {
                let step_type_name = annotations_map.get(step_type).unwrap().clone();
                writeln!(pil, "// === Step Type {} Setup ===", step_type_name).unwrap(); // Separator comment.

                let is_last_step_instance = 1
                    == *self
                        .step_types_instantiations
                        .get(step_type)
                        .unwrap()
                        .last()
                        .unwrap();

                let step_type_name = annotations_map.get(step_type).unwrap().clone();

                // Create constraint statements.
                if let Some(constraints) = self.constraints.get(step_type) {
                    for expr in constraints {
                        // `convert_to_pil_expr_string` recursively converts expressions to PIL
                        // strings, using standardized variable names from
                        // `annotations_map`.
                        let expr_string = convert_to_pil_expr_string(expr.clone(), annotations_map);
                        // Each constraint is in the format of `step_type * constraint = 0`, where
                        // `step_type` is a fixed step selector column and
                        // `constraint` the actual constraint expression.
                        writeln!(pil, "{} * {} = 0;", step_type_name, expr_string).unwrap();
                    }
                }

                // Create transition constraint statements, which have the same formats as regular
                // constraints.
                if let Some(transitions) = self.transitions.get(step_type) {
                    for expr in transitions {
                        let expr_string = convert_to_pil_expr_string(expr.clone(), annotations_map);
                        // Disable transition constraint in the last step instance.
                        if is_last_step_instance {
                            writeln!(
                                pil,
                                "(1 - ISLAST) * {} * {} = 0;",
                                step_type_name, expr_string
                            )
                            .unwrap();
                        } else {
                            writeln!(pil, "{} * {} = 0;", step_type_name, expr_string).unwrap();
                        }
                    }
                }

                // Create lookup statements. Note that there's no lookup table in PIL, so we only
                // need to convert lookups.
                if let Some(lookups) = self.lookups.get(step_type) {
                    for lookup in lookups {
                        let mut lookup_source: Vec<String> = Vec::new();
                        let mut lookup_destination: Vec<String> = Vec::new();
                        for (src, dest) in lookup {
                            lookup_source
                                .push(convert_to_pil_expr_string(src.clone(), annotations_map));
                            lookup_destination
                                .push(convert_to_pil_expr_string(dest.clone(), annotations_map));
                        }
                        // PIL lookups have the format of `step_type { lookup_sources } in {
                        // lookup_destinations }`.
                        writeln!(
                            pil,
                            "{} {{{}}} in {{{}}} ",
                            step_type_name,
                            lookup_source.join(", "),
                            lookup_destination.join(", ")
                        )
                        .unwrap();
                    }
                }
            }
        }

        if self.first_step.is_some() || self.last_step.is_some() {
            writeln!(pil, "// === Circuit Setup ===").unwrap();
        }

        // Create constraint for `pragma_first_step`, i.e. constraining step type of the first step
        // instance.
        if let Some(first_step) = self.first_step {
            let first_step_name = annotations_map.get(&first_step).unwrap().clone();
            writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name).unwrap();
        }

        // // Create constraint for `pragma_last_step`, i.e. constraining step type of the last step
        // instance.
        if let Some(last_step) = self.last_step {
            let last_step_name = annotations_map.get(&last_step).unwrap().clone();
            writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name).unwrap();
        }

        writeln!(pil, "// ===== END OF CIRCUIT: {} =====", self.circuit_name).unwrap();
        writeln!(pil).unwrap(); // Separator row for the circuit.

        pil
    }
}

#[allow(non_snake_case)]
/// User generate PIL code using this function. User needs to supply AST, TraceWitness, and a name
/// string for the circuit.
pub fn chiquito2Pil<F: Clone + Debug, TraceArgs>(
    ast: Circuit<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
    circuit_name: String,
) -> String {
    // Create annotations map. Note that internal signals defined in different step types will be
    // duplicated.
    let mut annotations_map = HashMap::new();

    // First add all annotations from the AST. Replace space because they will break the constraints
    // in PIL.
    for (key, value) in &ast.annotations {
        annotations_map.insert(*key, value.replace(' ', "_"));
    }

    // Next, add all annotations from each step type.
    for step_type in ast.step_types.values() {
        for (key, value) in &step_type.annotations {
            annotations_map.insert(*key, value.replace(' ', "_"));
        }
    }

    // Next, generate PIL IR.
    let pil_ir = PilCircuit::from_ast_and_witness(ast, witness, circuit_name);

    // Finally, generate PIL code given the IR and annotations map.
    pil_ir.generate_pil_given_annotations(&annotations_map)
}

#[allow(non_snake_case)]
/// User generate PIL code for super circuit using this function.
/// User needs to supply a Vec<String> for `circuit_names`, the order of which should be the same as
/// the order of calling `sub_circuit()` function.
pub fn chiquitoSuperCircuit2Pil<F: Debug + Field, MappingArgs>(
    super_circuit: SuperCircuit<F, MappingArgs>,
    super_trace_witnesses: HashMap<UUID, TraceWitness<F>>,
    circuit_names: Vec<String>,
) -> String {
    // super_asts, a Vec<ASTCircuit>, is a field added to SuperCircuit to support the PIL backend.
    let super_asts = super_circuit.get_super_asts();
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
        // referring to variables in PIL is there are more than one circuit.
        super_circuit_annotations_map.extend(annotations_map.into_iter().map(
            |(uuid, annotation)| {
                (
                    uuid,
                    format!("{}.{}", circuit_name.clone(), annotation.replace(' ', "_")),
                )
            },
        ));

        // Finally, get annotations for the circuit names.
        super_circuit_annotations_map.insert(ast.id, circuit_name.clone());
    }

    // Create a mapping from AST id to IR id, which is needed to link from AST to TraceWitness,
    // because TraceWitness only stores IR id.
    let ast_id_to_ir_id_mapping = super_circuit.get_ast_id_to_ir_id_mapping();

    let mut pil = String::new(); // The string to return.

    // For each AST, find its corresponding TraceWitness. Note that some AST might not have a
    // corresponding TraceWitness, so witness is an Option.
    for (ast, circuit_name) in super_asts.iter().zip(circuit_names.iter()) {
        let witness = super_trace_witnesses.get(ast_id_to_ir_id_mapping.get(&ast.id).unwrap());

        // Create PIL IR
        let pil_ir =
            PilCircuit::from_ast_and_witness(ast.clone(), witness.cloned(), circuit_name.clone());

        // Generate PIL code given the IR and annotations map.
        let pil_circuit = pil_ir.generate_pil_given_annotations(&super_circuit_annotations_map);
        writeln!(pil, "{}", pil_circuit).unwrap();
    }

    pil
}

// Convert expression to PIL string recursively. Coding this up separately because PIL has different
// syntax for queries.
fn convert_to_pil_expr_string<F: Debug + Clone>(
    expr: Expr<F, Queriable<F>>,
    annotations_map: &HashMap<UUID, String>,
) -> String {
    match expr {
        Expr::Const(constant) => format!("{:?}", constant),
        Expr::Sum(sum) => {
            let mut expr_string = String::new();
            for (index, expr) in sum.iter().enumerate() {
                expr_string += convert_to_pil_expr_string(expr.clone(), annotations_map).as_str();
                if index != sum.len() - 1 {
                    expr_string += " + ";
                }
            }
            format!("({})", expr_string)
        }
        Expr::Mul(mul) => {
            let mut expr_string = String::new();
            for (index, expr) in mul.iter().enumerate() {
                expr_string += convert_to_pil_expr_string(expr.clone(), annotations_map).as_str();
                if index != mul.len() - 1 {
                    expr_string += " * ";
                }
            }
            format!("({})", expr_string)
        }
        Expr::Neg(neg) => format!("(-{})", convert_to_pil_expr_string(*neg, annotations_map)),
        Expr::Pow(pow, power) => {
            format!(
                "({})^{}",
                convert_to_pil_expr_string(*pow, annotations_map),
                power
            )
        }
        Expr::Query(queriable) => convert_to_pil_queriable_string(queriable, annotations_map),
        Expr::Halo2Expr(_) => {
            panic!("Halo2 native expression not supported by PIL backend.")
        }
    }
}

// Convert queriable to PIL string recursively. Major differences are: 1. PIL rotations are in the
// format of an apostrophe after the signal; 2. PIL only supports the next rotation, so there's no
// previous or arbitrary rotation.
fn convert_to_pil_queriable_string<F>(
    query: Queriable<F>,
    annotations_map: &HashMap<UUID, String>,
) -> String {
    match query {
        Queriable::Internal(s) => annotations_map.get(&s.uuid()).unwrap().clone(),
        Queriable::Forward(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone();
            if !rot {
                annotation
            } else {
                format!("{}'", annotation)
            }
        }
        Queriable::Shared(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone();
            if rot == 0 {
                annotation
            } else if rot == 1 {
                format!("{}'", annotation)
            } else {
                panic!(
                    "PIL backend does not support shared signal with rotation other than 0 or 1."
                )
            }
        }
        Queriable::Fixed(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone();
            if rot == 0 {
                annotation
            } else if rot == 1 {
                format!("{}'", annotation)
            } else {
                panic!("PIL backend does not support fixed signal with rotation other than 0 or 1.")
            }
        }
        Queriable::StepTypeNext(s) => format!("{}'", annotations_map.get(&s.uuid()).unwrap()),
        Queriable::Halo2AdviceQuery(_, _) => {
            panic!("Halo2 native advice query not supported by PIL backend.")
        }
        Queriable::Halo2FixedQuery(_, _) => {
            panic!("Halo2 native fixed query not supported by PIL backend.")
        }
        Queriable::_unaccessible(_) => todo!(),
    }
}
