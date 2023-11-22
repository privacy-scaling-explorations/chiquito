use crate::{
    ast::{query::Queriable, Circuit},
    field::Field,
    pil::{compiler::powdr_pil::compile, ir::powdr_pil::PilCircuit},
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
    let pil_ir = compile(ast, witness, circuit_name);

    // Finally, generate PIL code given the IR and annotations map.
    generate_pil_given_annotations(&pil_ir, &annotations_map)
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
        let pil_ir = compile(ast.clone(), witness.cloned(), circuit_name.clone());

        // Generate PIL code given the IR and annotations map.
        let pil_circuit = generate_pil_given_annotations(&pil_ir, &super_circuit_annotations_map);
        writeln!(pil, "{}", pil_circuit).unwrap();
    }

    pil
}

// Generate PIL code given the IR of a single PIL circuit. Need to supply `annotations_map`,
// which only need to contain annotations for the circuit's own components if we are converting
// a standalone circuit. If we are converting a super circuit, `annotations_map` also needs to
// contain annotations for components outside the circuit.
fn generate_pil_given_annotations<F: Clone + Debug>(
    pil_ir: &PilCircuit<F>,
    annotations_map: &HashMap<UUID, String>,
) -> String {
    let mut pil = String::new(); // The string to return.

    writeln!(
        pil,
        "// ===== START OF CIRCUIT: {} =====",
        pil_ir.circuit_name
    )
    .unwrap();

    // Namespace is equivalent to a circuit in PIL. Note that we default `circuit_name` to
    // "Circuit" unless supplied.
    writeln!(
        pil,
        "constant %NUM_STEPS_{} = {};",
        pil_ir.circuit_name.to_uppercase(),
        pil_ir.num_steps
    )
    .unwrap();
    writeln!(
        pil,
        "namespace {}(%NUM_STEPS_{});",
        pil_ir.circuit_name.to_uppercase(),
        pil_ir.circuit_name.to_uppercase()
    )
    .unwrap();

    // Declare witness columns in PIL.
    generate_pil_witness_columns(&mut pil, pil_ir, annotations_map);

    // Convert fixed signals and their assignments in Chiquito to fixed columns in PIL.
    generate_pil_fixed_columns(&mut pil, pil_ir, annotations_map);

    // Create a step selector fixed column in PIL for each step type.
    generate_pil_step_selector_columns(&mut pil, pil_ir, annotations_map);

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
        pil_ir.circuit_name.to_uppercase()
    )
    .unwrap();

    // Iterate over step types to create constraint statements and lookups.
    generate_pil_step_types(&mut pil, pil_ir, annotations_map);

    if pil_ir.first_step.is_some() || pil_ir.last_step.is_some() {
        writeln!(pil, "// === Circuit Setup ===").unwrap();
    }

    // Create constraint for `pragma_first_step`, i.e. constraining step type of the first step
    // instance.
    if let Some(first_step) = pil_ir.first_step {
        let first_step_name = annotations_map.get(&first_step).unwrap().clone();
        writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name).unwrap();
    }

    // // Create constraint for `pragma_last_step`, i.e. constraining step type of the last step
    // instance.
    if let Some(last_step) = pil_ir.last_step {
        let last_step_name = annotations_map.get(&last_step).unwrap().clone();
        writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name).unwrap();
    }

    writeln!(
        pil,
        "// ===== END OF CIRCUIT: {} =====",
        pil_ir.circuit_name
    )
    .unwrap();
    writeln!(pil).unwrap(); // Separator row for the circuit.

    pil
}

fn generate_pil_witness_columns<F>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    annotations_map: &HashMap<UUID, String>,
) {
    if !pil_ir.col_witness.is_empty() {
        writeln!(pil, "// === Witness Columns for Signals ===").unwrap();
        let mut col_witness = String::from("col witness ");

        let mut col_witness_vars = pil_ir
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
}

fn generate_pil_fixed_columns<F: Debug>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    annotations_map: &HashMap<UUID, String>,
) {
    if !pil_ir.fixed_signals.is_empty() {
        writeln!(pil, "// === Fixed Columns for Signals ===").unwrap();
        for (fixed_signal_id, assignments) in pil_ir.fixed_signals.iter() {
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
}

fn generate_pil_step_selector_columns<F: Clone>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    annotations_map: &HashMap<UUID, String>,
) {
    if !pil_ir.step_types_instantiations.is_empty() {
        writeln!(pil, "// === Fixed Columns for Step Type Selectors ===").unwrap();
        for (step_type_id, step_type_instantiation) in pil_ir.step_types_instantiations.iter() {
            let step_type_name = annotations_map.get(step_type_id).unwrap().clone();
            let mut step_type_selector = String::new();
            write!(step_type_selector, "col fixed {} = [", step_type_name).unwrap();

            for (index, step_instance) in step_type_instantiation.iter().enumerate() {
                write!(step_type_selector, "{}", step_instance).unwrap();
                if index == pil_ir.num_steps - 1 {
                    write!(step_type_selector, "]").unwrap();
                } else {
                    write!(step_type_selector, ", ").unwrap();
                }
            }
            writeln!(pil, "{}", step_type_selector).unwrap();
        }
    }
}

fn generate_pil_step_types<F: Debug + Clone>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    annotations_map: &HashMap<UUID, String>,
) {
    if !pil_ir.step_types.is_empty() {
        for step_type in &pil_ir.step_types {
            let step_type_name = annotations_map.get(step_type).unwrap().clone();
            writeln!(pil, "// === Step Type {} Setup ===", step_type_name.clone()).unwrap(); // Separator comment.

            // Create constraint statements.
            generate_pil_constraints(
                pil,
                pil_ir,
                step_type,
                step_type_name.clone(),
                annotations_map,
            );

            // Create transition constraint statements, which have the same formats as regular
            // constraints.
            generate_pil_transitions(
                pil,
                pil_ir,
                step_type,
                step_type_name.clone(),
                annotations_map,
            );

            // Create lookup statements. Note that there's no lookup table in PIL, so we only
            // need to convert lookups.
            generate_pil_lookups(pil, pil_ir, step_type, step_type_name, annotations_map);
        }
    }
}

fn generate_pil_constraints<F: Debug + Clone>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    step_type: &UUID,
    step_type_name: String,
    annotations_map: &HashMap<UUID, String>,
) {
    if let Some(constraints) = pil_ir.constraints.get(step_type) {
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
}

fn generate_pil_transitions<F: Debug + Clone>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    step_type: &UUID,
    step_type_name: String,
    annotations_map: &HashMap<UUID, String>,
) {
    let is_last_step_instance = 1
        == *pil_ir
            .step_types_instantiations
            .get(step_type)
            .unwrap()
            .last()
            .unwrap();

    if let Some(transitions) = pil_ir.transitions.get(step_type) {
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
}

fn generate_pil_lookups<F: Debug + Clone>(
    pil: &mut String,
    pil_ir: &PilCircuit<F>,
    step_type: &UUID,
    step_type_name: String,
    annotations_map: &HashMap<UUID, String>,
) {
    if let Some(lookups) = pil_ir.lookups.get(step_type) {
        for lookup in lookups {
            let mut lookup_source: Vec<String> = Vec::new();
            let mut lookup_destination: Vec<String> = Vec::new();
            for (src, dest) in lookup {
                lookup_source.push(convert_to_pil_expr_string(src.clone(), annotations_map));
                lookup_destination.push(convert_to_pil_expr_string(dest.clone(), annotations_map));
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
