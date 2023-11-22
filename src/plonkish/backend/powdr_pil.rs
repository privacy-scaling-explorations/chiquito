use crate::{
    ast::{query::Queriable, Circuit, StepType},
    field::Field,
    plonkish::ir::sc::SuperCircuit,
    poly::Expr,
    util::UUID,
    wit_gen::TraceWitness,
};
use std::{
    collections::HashMap,
    fmt::{Debug, Write}, hash::Hash,
};
extern crate regex;

/// User creates ChiquitoPil object and call `to_pil()` on it to obtain PIL program string for a
/// standalone circuit. To convert a super circuit, the program will create multiple ChiquitoPil
/// objects.
pub struct ChiquitoPil<F, TraceArgs> {
    ast: Circuit<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
}

impl<F: Debug, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn new(ast: Circuit<F, TraceArgs>, witness: Option<TraceWitness<F>>) -> Self {
        Self { ast, witness }
    }
}

impl<F: Debug + Clone, TraceArgs> ChiquitoPil<F, TraceArgs> {
    /// The main function to call on a standalone circuit to obtain PIL program string.
    pub fn to_pil(self: &ChiquitoPil<F, TraceArgs>) -> String {
        self.to_pil_single_circuit(None)
    }

    // This function is called internally with `annotations_map = None` when converting a standalone
    // circuit. It's called internally with `annotations_map = Some` when converting a super
    // circuit.
    pub fn to_pil_single_circuit(
        self: &ChiquitoPil<F, TraceArgs>,
        mut annotations_map: Option<HashMap<UUID, (UUID, String)>>,
    ) -> String {
        let mut pil = String::new(); // The string to return

        // If `annotations_map` is not provided for the super circuit, we are converting a
        // standalone circuit. In this case, we declare the `NUM_STEPS` constant and the
        // namespace with `Circuit` as the generic name for the circuit.
        if annotations_map.is_none() {
            writeln!(pil, "constant %NUM_STEPS = {};", self.ast.num_steps).unwrap();
            writeln!(pil, "namespace Circuit(%NUM_STEPS);",).unwrap();
        } else {
            // If `anotations_map` is provided, we are converting a super circuit.
            // In this case, we declare the `NUM_STEPS` constant and the namespace with the circuit
            // name obtained from the annotations map.
            let circuit_name = annotations_map
                .as_ref()
                .unwrap()
                .get(&self.ast.id)
                .unwrap()
                .clone()
                .1;
            writeln!(
                pil,
                "constant %NUM_STEPS_{} = {};",
                circuit_name, self.ast.num_steps
            )
            .unwrap();
            writeln!(pil, "namespace {}(%NUM_STEPS);", circuit_name).unwrap();
        }

        // If `annotations_map` is not provided for the super circuit, we are converting a
        // standalone circuit. In this case, we create an annotation map for all signals and
        // step types. Then, we categorize annotations for step types and different signals
        // types in multiple Vec<UUID>. Note that internal signals defined in different step
        // types will be duplicated.
        if annotations_map.is_none() {
            let mut new_annotations_map = HashMap::new();

            // To create an `annotations_map` for the standalone circuit, first add all annotations
            // from the AST. Replace space because they will break the constraints in
            // PIL.
            for (key, value) in &self.ast.annotations {
                new_annotations_map.insert(*key, (self.ast.id, value.replace(' ', "_")));
            }

            // Next, add all annotations from each step type.
            for step_type in self.ast.step_types.values() {
                for (key, value) in &step_type.annotations {
                    new_annotations_map.insert(*key, (self.ast.id, value.replace(' ', "_")));
                }
            }

            // To be consistent with the input parameter of `to_pil()`, return the annotations_map
            // as an Option.
            annotations_map = Some(new_annotations_map);
        }

        // Create a Vec<UUID> for witness columns in PIL, corresponding to internal signals, forward
        // signals, and shared signals in Chiquito. This vector will be used later for
        // witness column declaration in PIL.
        let mut col_witness_uuids: Vec<UUID> = Vec::new();

        // Collect UUIDs of internal signals stored at the step type level.
        for step_type in self.ast.step_types.values() {
            col_witness_uuids.extend::<Vec<UUID>>(
                step_type
                    .signals
                    .iter()
                    .map(|signal| signal.uuid())
                    .collect(),
            );
        }

        // Collect UUIDs of forward signals stored at the circuit level.
        col_witness_uuids.extend::<Vec<UUID>>(
            self.ast
                .forward_signals
                .iter()
                .map(|forward_signal| forward_signal.uuid())
                .collect(),
        );

        // Collect UUIDs of shared signals stored at the circuit level.
        col_witness_uuids.extend::<Vec<UUID>>(
            self.ast
                .shared_signals
                .iter()
                .map(|shared_signal| shared_signal.uuid())
                .collect(),
        );

        // Create a Vec<UUID> for fixed columns in PIL, corresponding to fixed signals in Chiquito.
        // This vector will be used later for fixed column declaration in PIL.
        let col_fixed_uuids = self
            .ast
            .fixed_signals
            .iter()
            .map(|fixed_signal| fixed_signal.uuid())
            .collect::<Vec<UUID>>();

        // Create another Vec<UUID> for all step types in Chiquito.
        // We will declare step type selectors as fixed columns in PIL as well.
        let col_fixed_step_types_uuids: Vec<UUID> = self.ast.step_types.keys().cloned().collect();

        // If `annotations_map` is not provided for the super circuit, we are converting a
        // standalone circuit. Make sure that annotations can only ever be witness columns,
        // fixed columns, or step types.
        if annotations_map.is_none() {
            assert!(
                col_witness_uuids.len() + col_fixed_uuids.len() + col_fixed_step_types_uuids.len()
                    == annotations_map.as_ref().unwrap().len()
            );
        }

        // Declare witness columns in PIL.
        if !col_witness_uuids.is_empty() {
            let mut col_witness = String::from("col witness ");

            let mut col_witness_vars = col_witness_uuids
                .iter()
                .map(|uuid| {
                    annotations_map
                        .as_ref()
                        .unwrap()
                        .get(uuid)
                        .unwrap()
                        .clone()
                        .1
                })
                .collect::<Vec<String>>();

            // Get unique witness column annotations, because the same internal signal across
            // different step types have different UUIDs and therefore appear multiple times.
            col_witness_vars.sort();
            col_witness_vars.dedup();
            col_witness = col_witness + col_witness_vars.join(", ").as_str() + ";";
            writeln!(pil, "{}", col_witness).unwrap();
        }

        // Declare fixed columns for variables (not step types).
        if !col_fixed_uuids.is_empty() {
            let mut col_fixed = String::from("col fixed ");
            let col_fixed_vars = col_fixed_uuids
                .iter()
                .map(|uuid| {
                    annotations_map
                        .as_ref()
                        .unwrap()
                        .get(uuid)
                        .unwrap()
                        .clone()
                        .1
                })
                .collect::<Vec<String>>();
            col_fixed = col_fixed + col_fixed_vars.join(", ").as_str() + ";";
            writeln!(pil, "{}", col_fixed).unwrap();
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
            "col fixed ISLAST(i) {{ match i {{ %NUM_STEPS - 1 => 1, _ => 0 }} }};"
        )
        .unwrap();

        // Iterate over step types to create constraint statements, fixed columns for step type
        // selectors, and lookups.
        if !self.ast.step_types.is_empty() && self.witness.is_some() {
            for step_type in self.ast.step_types.values() {
                let step_type_name = annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&step_type.uuid())
                    .unwrap()
                    .clone()
                    .1;
                writeln!(pil, "// === Step Type {} ===", step_type_name).unwrap(); // Separator comment.
                let mut step_type_selector = String::new();
                write!(step_type_selector, "col fixed {} = [", step_type_name).unwrap();
                // Create the step selector fixed column by looping over the TraceWitness object,
                // which contains Vec<StepInstance>. Therefore, each step type will
                // be a row in PIL.
                for (index, step_instance) in self
                    .witness
                    .clone()
                    .unwrap()
                    .step_instances
                    .iter()
                    .enumerate()
                {
                    if step_instance.step_type_uuid == step_type.uuid() {
                        write!(step_type_selector, "1").unwrap();
                    } else {
                        write!(step_type_selector, "0").unwrap();
                    }
                    if index == self.witness.clone().unwrap().step_instances.len() - 1 {
                        write!(step_type_selector, "]").unwrap();
                    } else {
                        write!(step_type_selector, ", ").unwrap();
                    }
                }
                writeln!(pil, "{}", step_type_selector).unwrap();
                let is_last_step_instance = step_type.uuid()
                    == self
                        .witness
                        .clone()
                        .unwrap()
                        .step_instances
                        .last()
                        .unwrap()
                        .step_type_uuid;
                // Call `to_pil()` on step type to convert the constraints and lookups.
                writeln!(
                    pil,
                    "{}",
                    step_type
                        .to_pil(annotations_map.as_ref().unwrap(), is_last_step_instance)
                        .as_str()
                )
                .unwrap();
            }
        }

        // Create constraint for `pragma_first_step`, i.e. constraining step type of the first step
        // instance.
        if let Some(first_step) = self.ast.first_step {
            let first_step_name = annotations_map
                .as_ref()
                .unwrap()
                .get(&first_step)
                .unwrap()
                .clone()
                .1;
            writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name).unwrap();
        }

        // // Create constraint for `pragma_last_step`, i.e. constraining step type of the last step
        // instance.
        if let Some(last_step) = self.ast.last_step {
            let last_step_name = annotations_map
                .as_ref()
                .unwrap()
                .get(&last_step)
                .unwrap()
                .clone()
                .1;
            writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name).unwrap();
        }

        // Convert fixed assignments in Chiquito to fixed columns in PIL.
        if let Some(fixed_assignments) = &self.ast.fixed_assignments {
            for (queriable, assignments) in fixed_assignments.iter() {
                let fixed_name = annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&queriable.uuid())
                    .unwrap()
                    .clone()
                    .1;
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
        writeln!(pil).unwrap();
        writeln!(pil).unwrap(); // Separator rows for the circuit.
        pil
    }
}

/// User creates ChiquitoPilSuperCircuit object and call `to_pil()` on it to obtain PIL program
/// string for a super circuit. To convert a super circuit, the program will create multiple
/// ChiquitoPil objects.
pub struct ChiquitoPilSuperCircuit<F> {
    super_ast: HashMap<UUID, Circuit<F, ()>>,
    super_witness: HashMap<UUID, Option<TraceWitness<F>>>,
    circuit_names: HashMap<UUID, String>,
}

impl<F: Debug> ChiquitoPilSuperCircuit<F> {
    fn default() -> Self {
        Self {
            super_ast: HashMap::new(),
            super_witness: HashMap::new(),
            circuit_names: HashMap::new(),
        }
    }

    // `witness` is an option, because not all ASTs have a corresponding TraceWitness.
    fn add(&mut self, ast: Circuit<F, ()>, witness: Option<TraceWitness<F>>, circuit_name: String) {
        let id = ast.id;
        self.super_ast.insert(id, ast);
        self.super_witness.insert(id, witness);
        self.circuit_names.insert(id, circuit_name);
    }
}

#[allow(non_snake_case)]
/// User creates ChiquitoPilSuperCircuit objects using this function.
/// User needs to supply a Vec<String> for `circuit_names`, the order of which should be the same as
/// the order of calling `sub_circuit()` function. `args` are the input arguments supplied to the
/// mapping generator of the super circuit.
pub fn chiquitoSuperCircuit2Pil<F: Debug + Field + Hash, MappingArgs>(
    super_circuit: SuperCircuit<F, MappingArgs>,
    args: MappingArgs,
    circuit_names: Vec<String>,
) -> ChiquitoPilSuperCircuit<F> {
    let mut chiquito_pil_super_circuit = ChiquitoPilSuperCircuit::default();

    // super_asts, a Vec<ASTCircuit>, is a field added to SuperCircuit to support the PIL backend.
    let super_asts = super_circuit.get_super_asts();
    assert!(super_asts.len() == circuit_names.len());

    // Create a mapping from AST id to IR id, which is needed to link from AST to TraceWitness,
    // because TraceWitness only stores IR id.
    let ast_id_to_ir_id_mapping = super_circuit.get_ast_id_to_ir_id_mapping();

    // `super_trace_witnesses` is a mapping from IR id to TraceWitness. However, not all ASTs have a
    // corresponding TraceWitness.
    let super_trace_witnesses = super_circuit
        .get_mapping()
        .generate_super_trace_witnesses(args);

    // For each AST, add the AST, its corresponding TraceWitness, and the `circuit_name` to the
    // ChiquitoPilSuperCircuit object. Note that some AST might not have a corresponding
    // TraceWitness, so witness is an Option.
    for (ast, circuit_name) in super_asts.iter().zip(circuit_names.iter()) {
        let witness = super_trace_witnesses.get(ast_id_to_ir_id_mapping.get(&ast.id).unwrap());
        chiquito_pil_super_circuit.add(ast.clone(), witness.cloned(), circuit_name.clone());
    }

    chiquito_pil_super_circuit
}

impl<F: Debug + Clone> ChiquitoPilSuperCircuit<F> {
    /// User invokes this function on a ChiquitoPilSuperCircuit object to obtain the PIL program
    /// string.
    pub fn to_pil(self: &ChiquitoPilSuperCircuit<F>) -> String {
        assert!(self.super_ast.len() == self.super_witness.len());
        let mut pil = String::new();

        // Get annotations map for the super circuit, which is a HashMap of object UUID to (AST
        // UUID, object annotation).
        let mut super_circuit_annotations_map: HashMap<UUID, (UUID, String)> = HashMap::new();

        // Loop over each AST.
        for (ast_id, ast) in self.super_ast.iter() {
            let mut annotations_map: HashMap<UUID, String> = HashMap::new();
            let circuit_name = self.circuit_names.get(ast_id).unwrap().clone();

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
                        (
                            *ast_id,
                            format!("{}.{}", circuit_name, annotation.replace(' ', "_")),
                        ),
                    )
                },
            ));

            // Finally, get annotations for the circuit names.
            super_circuit_annotations_map.insert(*ast_id, (*ast_id, circuit_name));
        }

        // Create a ChiquitoPil object for each (AST, witness) pair and call
        // `to_pil_single_circuit()` on it.
        for (id, ast) in self.super_ast.iter() {
            let witness = self.super_witness.get(id).unwrap();
            let chiquito_pil = ChiquitoPil::new(ast.clone(), witness.clone());
            pil += chiquito_pil
                .to_pil_single_circuit(Some(super_circuit_annotations_map.clone()))
                .as_str();
        }

        pil
    }
}

impl<F: Debug + Clone> StepType<F> {
    // Called by the `to_pil` function of ChiquitoPil.
    fn to_pil(
        self: &StepType<F>,
        annotations_map: &HashMap<UUID, (UUID, String)>,
        is_last_step_instance: bool,
    ) -> String {
        let mut pil = String::new();
        let step_type_name = annotations_map.get(&self.uuid()).unwrap().clone().1;

        // Create constraint statements.
        for constraint in &self.constraints {
            // `convert_to_pil_expr_string` recursively converts expressions to PIL strings, using
            // standardized variable names from `annotations_map`.
            let expr = convert_to_pil_expr_string(constraint.expr.clone(), annotations_map);
            // Each constraint is in the format of `step_type * constraint = 0`, where `step_type`
            // is a fixed step selector column and `constraint` the actual constraint expression.
            writeln!(pil, "{} * {} = 0;", step_type_name, expr).unwrap();
        }

        // Create transition constraint statements, which have the same formats as regular
        // constraints.
        for transition in &self.transition_constraints {
            let expr = convert_to_pil_expr_string(transition.expr.clone(), annotations_map);
            // Disable transition constraint in the last step instance.
            if is_last_step_instance {
                writeln!(pil, "(1 - ISLAST) * {} * {} = 0;", step_type_name, expr).unwrap();
            } else {
                writeln!(pil, "{} * {} = 0;", step_type_name, expr).unwrap();
            }
        }

        // Create lookup statements. Note that there's no lookup table in PIL, so we only need to
        // convert lookups.
        for lookup in &self.lookups {
            let mut lookup_source: Vec<String> = Vec::new();
            let mut lookup_destination: Vec<String> = Vec::new();
            for (src, dest) in lookup.exprs.iter() {
                lookup_source.push(convert_to_pil_expr_string(
                    src.expr.clone(),
                    annotations_map,
                ));
                lookup_destination.push(convert_to_pil_expr_string(dest.clone(), annotations_map));
            }
            // PIL lookups have the format of `step_type { lookup_sources } in { lookup_destinations
            // }`.
            writeln!(
                pil,
                "{} {{ {} }} in {{ {} }} ",
                step_type_name,
                lookup_source.join(", "),
                lookup_destination.join(", ")
            )
            .unwrap();
        }
        pil
    }
}

// Convert expression to PIL string recursively. Coding this up separately because PIL has different
// syntax for queries.
fn convert_to_pil_expr_string<F: Debug + Clone>(
    expr: Expr<F, Queriable<F>>,
    annotations_map: &HashMap<UUID, (UUID, String)>,
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
    annotations_map: &HashMap<UUID, (UUID, String)>,
) -> String {
    match query {
        Queriable::Internal(s) => annotations_map.get(&s.uuid()).unwrap().clone().1,
        Queriable::Forward(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone().1;
            if !rot {
                annotation
            } else {
                format!("{}'", annotation)
            }
        }
        Queriable::Shared(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone().1;
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
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone().1;
            if rot == 0 {
                annotation
            } else if rot == 1 {
                format!("{}'", annotation)
            } else {
                panic!("PIL backend does not support fixed signal with rotation other than 0 or 1.")
            }
        }
        Queriable::StepTypeNext(s) => format!("{}'", annotations_map.get(&s.uuid()).unwrap().1),
        Queriable::Halo2AdviceQuery(_, _) => {
            panic!("Halo2 native advice query not supported by PIL backend.")
        }
        Queriable::Halo2FixedQuery(_, _) => {
            panic!("Halo2 native fixed query not supported by PIL backend.")
        }
        Queriable::_unaccessible(_) => todo!(),
    }
}
