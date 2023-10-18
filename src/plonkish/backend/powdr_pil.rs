// #[derive(Clone)]
// pub struct Circuit<F, TraceArgs> {
//     pub step_types: HashMap<UUID, Rc<StepType<F>>>,

//     pub forward_signals: Vec<ForwardSignal>,
//     pub shared_signals: Vec<SharedSignal>,
//     pub fixed_signals: Vec<FixedSignal>,
//     pub halo2_advice: Vec<ImportedHalo2Advice>,
//     pub halo2_fixed: Vec<ImportedHalo2Fixed>,
//     pub exposed: Vec<(Queriable<F>, ExposeOffset)>,

//     pub annotations: HashMap<UUID, String>,

//     pub trace: Option<Rc<Trace<F, TraceArgs>>>,
//     pub fixed_assignments: Option<FixedAssignment<F>>,

//     pub first_step: Option<StepTypeUUID>,
//     pub last_step: Option<StepTypeUUID>,
//     pub num_steps: usize,
//     pub q_enable: bool,

//     pub id: UUID,
// }

// pub struct StepType<F> {
//     id: StepTypeUUID,

//     pub name: String,
//     pub signals: Vec<InternalSignal>,
//     pub constraints: Vec<Constraint<F>>,
//     pub transition_constraints: Vec<TransitionConstraint<F>>,
//     pub lookups: Vec<Lookup<F>>,
//     pub annotations: HashMap<UUID, String>,
// }

use halo2_proofs::plonk::Assignment;

use crate::{
    ast::{query::Queriable, Circuit, StepType},
    field::Field,
    frontend::dsl::cb::lookup,
    plonkish::ir::{assignments, sc::SuperCircuit},
    poly::{Expr, ToExpr},
    util::UUID,
    wit_gen::TraceWitness,
};
use std::{
    collections::HashMap,
    fmt::{write, Debug, Write},
};
extern crate regex;

pub struct ChiquitoPil<F, TraceArgs> {
    ast: Circuit<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
}

impl<F: Debug, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn new(ast: Circuit<F, TraceArgs>, witness: Option<TraceWitness<F>>) -> Self {
        Self { ast, witness }
    }
}

pub struct ChiquitoPilSuperCircuit<F> {
    super_ast: HashMap<UUID, Circuit<F, ()>>,
    super_witness: HashMap<UUID, Option<TraceWitness<F>>>,
    circuit_names: Vec<String>,
}

impl<F: Debug> ChiquitoPilSuperCircuit<F> {
    pub fn default() -> Self {
        Self {
            super_ast: HashMap::new(),
            super_witness: HashMap::new(),
            circuit_names: Vec::new(),
        }
    }

    pub fn add(
        &mut self,
        ast: Circuit<F, ()>,
        witness: Option<TraceWitness<F>>,
        circuit_name: String,
    ) {
        let id = ast.id;
        self.super_ast.insert(id, ast);
        self.super_witness.insert(id, witness);
        self.circuit_names.push(circuit_name);
    }
}

#[allow(non_snake_case)]
pub fn chiquitoSuperCircuit2Pil<F: Debug + Field, MappingArgs>(
    super_circuit: SuperCircuit<F, MappingArgs>,
    args: MappingArgs,
    circuit_names: Vec<String>,
) -> ChiquitoPilSuperCircuit<F> {
    let mut chiquito_pil_super_circuit = ChiquitoPilSuperCircuit::default();

    // trace witnesses have the same id as ast
    let super_asts = super_circuit.get_super_asts();
    assert!(super_asts.len() == circuit_names.len());

    let ast_id_to_ir_id_mapping = super_circuit.get_ast_id_to_ir_id_mapping();
    // super_trace_witnesses have ir_id as key
    let super_trace_witnesses = super_circuit
        .get_mapping()
        .generate_super_trace_witnesses(args);
    // println!("super_witness:");
    // println!("{:?}", super_trace_witnesses);
    // println!("super_trace_witnesses keys:");
    // println!("{:?}", super_trace_witnesses.keys());
    for ((id, ast), circuit_name) in super_asts.iter().zip(circuit_names.iter()) {
        // println!("{:?}", super_trace_witnesses.keys());
        // println!("ast_id: {}", id);
        let witness = super_trace_witnesses.get(ast_id_to_ir_id_mapping.get(&id).unwrap());
        chiquito_pil_super_circuit.add(ast.clone(), witness.cloned(), circuit_name.clone());
    }

    chiquito_pil_super_circuit
}

impl<F: Debug + Clone> ChiquitoPilSuperCircuit<F> {
    pub fn to_pil(self: &ChiquitoPilSuperCircuit<F>) -> String {
        assert!(self.super_ast.len() == self.super_witness.len());
        let mut pil = String::new();

        // get annotations map for supercircuit, HashMap of object UUID to (ast UUID, annotation)
        let mut super_annotations_map: HashMap<UUID, (UUID, String)> = HashMap::new();

        for ((ast_id, ast), circuit_name) in self.super_ast.iter().zip(self.circuit_names.iter()) {
            let mut annotations_map: HashMap<UUID, String> = HashMap::new();
            
            annotations_map.extend(ast.annotations.clone());
            for (_, step_type) in &ast.step_types {
                annotations_map.extend(step_type.annotations.clone());
            }
            super_annotations_map.extend(annotations_map.into_iter().map(|(uuid, annotation)| {
                (
                    uuid,
                    (
                        ast_id.clone(),
                        format!("{}.{}", circuit_name, annotation.replace(" ", "_")),
                    ),
                )
            }));
            super_annotations_map.insert(*ast_id, (*ast_id, circuit_name.clone()));
            println!("SUPER ANNOTATIONS MAP:");
            println!("{:?}", super_annotations_map.clone());
        }

        for (index, (id, ast)) in self.super_ast.iter().enumerate() {
            let witness = self.super_witness.get(id).unwrap();
            // println!("witness is some: {}", witness.is_some());
            // println!("super_witness:");
            // println!("{:?}", self.super_witness);
            // println!("ast id: {}", id);
            // currently name the circuits by their index in the super circuit
            // would ideally use a user supplied name
            let chiquito_pil = ChiquitoPil::new(ast.clone(), witness.clone());
            pil = pil
                + chiquito_pil
                    .to_pil(Some(super_annotations_map.clone()))
                    .as_str();
        }
        println!("{}", pil);
        pil
    }
}

impl<F: Debug + Clone, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn to_pil(
        self: &ChiquitoPil<F, TraceArgs>,
        mut annotations_map: Option<HashMap<UUID, (UUID, String)>>,
    ) -> String {
        // create new string buffer
        let mut pil = String::new();
        writeln!(pil, "constant %NUM_STEPS = {};", self.ast.num_steps);
        if annotations_map.is_none() {
            writeln!(pil, "namespace Circuit(%NUM_STEPS);",);
        } else {
            writeln!(
                pil,
                "namespace {}(%NUM_STEPS);",
                annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&self.ast.id)
                    .unwrap()
                    .clone()
                    .1
            );
        }

        // create annotation map for all signals and step types
        // categorize annotations for signals and step types in UUID vectors
        // note that internal signals defined in different step types will be duplicated
        if annotations_map.is_none() {
            let mut new_annotations_map = HashMap::new();

            // Convert the original annotations map
            for (key, value) in &self.ast.annotations {
                new_annotations_map.insert(*key, (self.ast.id, value.replace(" ", "_")));
            }

            // Convert the step_types annotations
            for (_, step_type) in &self.ast.step_types {
                for (key, value) in &step_type.annotations {
                    new_annotations_map.insert(*key, (self.ast.id, value.replace(" ", "_")));
                }
            }

            annotations_map = Some(new_annotations_map);
        }

        let mut col_witness_uuids: Vec<UUID> = Vec::new();
        for (_, step_type) in &self.ast.step_types {
            col_witness_uuids.extend::<Vec<UUID>>(
                step_type
                    .signals
                    .iter()
                    .map(|signal| signal.uuid())
                    .collect(),
            );
        }

        col_witness_uuids.extend::<Vec<UUID>>(
            self.ast
                .forward_signals
                .iter()
                .map(|forward_signal| forward_signal.uuid())
                .collect(),
        );
        col_witness_uuids.extend::<Vec<UUID>>(
            self.ast
                .shared_signals
                .iter()
                .map(|shared_signal| shared_signal.uuid())
                .collect(),
        );

        let mut col_fixed_uuids = self
            .ast
            .fixed_signals
            .iter()
            .map(|fixed_signal| fixed_signal.uuid())
            .collect::<Vec<UUID>>();
        let mut col_fixed_step_types_uuids: Vec<UUID> =
            self.ast.step_types.keys().cloned().collect();

        if annotations_map.is_none() {
            assert!(
                col_witness_uuids.len() + col_fixed_uuids.len() + col_fixed_step_types_uuids.len()
                    == annotations_map.as_ref().unwrap().len()
            );
        }

        // declare witness columns
        if !col_witness_uuids.is_empty() {
            let mut col_witness = String::from("col witness ");
            // get unique witness annotations
            let col_witness_vars = col_witness_uuids
                .iter()
                .map(|uuid| {
                    annotations_map
                        .as_ref()
                        .unwrap()
                        .get(&uuid)
                        .unwrap()
                        .clone()
                        .1
                })
                .collect::<Vec<String>>();
            col_witness = col_witness + col_witness_vars.join(", ").as_str() + ";";
            writeln!(pil, "{}", col_witness);
        }

        // declare non-step type fixed columns
        if !col_fixed_uuids.is_empty() {
            let mut col_fixed = String::from("col fixed ");
            // get unique witness annotations
            let col_fixed_vars = col_fixed_uuids
                .iter()
                .map(|uuid| {
                    annotations_map
                        .as_ref()
                        .unwrap()
                        .get(&uuid)
                        .unwrap()
                        .clone()
                        .1
                })
                .collect::<Vec<String>>();
            col_fixed = col_fixed + col_fixed_vars.join(", ").as_str() + ";";
            writeln!(pil, "{}", col_fixed);
        }

        // ISFIRST and ISLAST needed for pragma_first_step and pragma_last_step
        writeln!(
            pil,
            "col fixed ISFIRST(i) {{ match i {{ 0 => 1, _ => 0 }} }};"
        );
        writeln!(
            pil,
            "col fixed ISLAST(i) {{ match i {{ %NUM_STEPS - 1 => 1, _ => 0 }} }};"
        );

        // iterate over self.step_types
        // println!("self.witness.is_some() {}", self.witness.is_some());
        if !self.ast.step_types.is_empty() && self.witness.is_some() {
            for (_, step_type) in &self.ast.step_types {
                let step_type_name = annotations_map
                    .as_ref()
                    .unwrap()
                    .get(&step_type.uuid())
                    .unwrap()
                    .clone()
                    .1;
                writeln!(pil, "// == step type {} start ==", step_type_name).unwrap();
                let mut step_type_selector = String::new();
                write!(step_type_selector, "col fixed {} = [", step_type_name);
                for (index, step_instance) in self
                    .witness
                    .clone()
                    .unwrap()
                    .step_instances
                    .iter()
                    .enumerate()
                {
                    if step_instance.step_type_uuid == step_type.uuid() {
                        write!(step_type_selector, "1");
                    } else {
                        write!(step_type_selector, "0");
                    }
                    if index == self.witness.clone().unwrap().step_instances.len() - 1 {
                        write!(step_type_selector, "]");
                    } else {
                        write!(step_type_selector, ", ");
                    }
                    // println!("step instance: {:?}", step_instance.step_type_uuid);
                }
                writeln!(pil, "{}", step_type_selector);
                let is_last_step_instance = step_type.uuid()
                    == self
                        .witness
                        .clone()
                        .unwrap()
                        .step_instances
                        .last()
                        .unwrap()
                        .step_type_uuid;
                writeln!(
                    pil,
                    "{}",
                    step_type
                        .to_pil(annotations_map.as_ref().unwrap(), is_last_step_instance)
                        .as_str()
                );
                println!("ANNOTATIONS MAP:");
                println!("{:?}", annotations_map);
            }
        }

        // pragma_first_step
        if let Some(first_step) = self.ast.first_step {
            let first_step_name = annotations_map
                .as_ref()
                .unwrap()
                .get(&first_step)
                .unwrap()
                .clone()
                .1;
            writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name);
        }

        // pragma_last_step
        if let Some(last_step) = self.ast.last_step {
            let last_step_name = annotations_map
                .as_ref()
                .unwrap()
                .get(&last_step)
                .unwrap()
                .clone()
                .1;
            writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name);
        }

        // declare fixed assignments
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
                );
                writeln!(pil, "col fixed {} = [{}];", fixed_name, assignments_string);
            }
        }

        pil
    }
}

impl<F: Debug + Clone> StepType<F> {
    pub fn to_pil(
        self: &StepType<F>,
        annotations_map: &HashMap<UUID, (UUID, String)>,
        is_last_step_instance: bool,
    ) -> String {
        let mut pil = String::new();
        let step_type_name = annotations_map.get(&self.uuid()).unwrap().clone().1;
        for constraint in &self.constraints {
            let expr = convert_to_pil_expr_string(constraint.expr.clone(), annotations_map);

            writeln!(pil, "{} * {} = 0;", step_type_name, expr);
        }
        for transition in &self.transition_constraints {
            // apply convert_to_pil_rotation to the Debug string of transition.expr
            let expr = convert_to_pil_expr_string(transition.expr.clone(), annotations_map);
            // disable transition constraint in the last step instance
            if (is_last_step_instance) {
                writeln!(pil, "(1 - ISLAST) * {} * {} = 0;", step_type_name, expr);
            } else {
                writeln!(pil, "{} * {} = 0;", step_type_name, expr);
            }
        }
        for lookup in &self.lookups {
            let mut lookup_source: Vec<String> = Vec::new();
            let mut lookup_destination: Vec<String> = Vec::new();
            for(src, dest) in lookup.exprs.iter() {
                lookup_source.push(convert_to_pil_expr_string(src.expr.clone(), annotations_map));
                lookup_destination.push(convert_to_pil_expr_string(dest.clone(), annotations_map));
            }
            writeln!(pil, "{} {{ {} }} in {{ {} }} ", step_type_name, lookup_source.join(", "), lookup_destination.join(", "));
        }
        pil
    }
}

// fn convert_to_pil_rotation(expr: &str) -> String {
//     // replace non alphanumeric characters with _ except brackets + - * / ^
//     // let re = regex::Regex::new(r"[^\w\(\)+\-*/^]").unwrap();
//     // let expr = re.replazce_all(expr, "_").into_owned();
//     // convert rotation
//     let re = regex::Regex::new(r"next\((\w+)\)").unwrap(); // w+ is alphanumeric
//     re.replace_all(expr, "$1'").into_owned() // 1st capture group w+ and append with '
// }

pub fn convert_to_pil_expr_string<F: Debug + Clone>(
    expr: Expr<F, Queriable<F>>,
    annotations_map: &HashMap<UUID, (UUID, String)>,
) -> String {
    match expr {
        Expr::Const(constant) => format!("{:?}", constant),
        Expr::Sum(sum) => {
            let mut expr_string = String::new();
            for (index, expr) in sum.iter().enumerate() {
                expr_string = expr_string
                    + convert_to_pil_expr_string(expr.clone(), annotations_map).as_str();
                if index != sum.len() - 1 {
                    expr_string = expr_string + " + ";
                }
            }
            format!("({})", expr_string)
        }
        Expr::Mul(mul) => {
            let mut expr_string = String::new();
            for (index, expr) in mul.iter().enumerate() {
                expr_string = expr_string
                    + convert_to_pil_expr_string(expr.clone(), annotations_map).as_str();
                if index != mul.len() - 1 {
                    expr_string = expr_string + " * ";
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
        Expr::Query(queriable) => format!(
            "{}",
            convert_to_pil_queriable_string(queriable, annotations_map)
        ),
        Expr::Halo2Expr(expression) => {
            panic!("Halo2 native expression not supported by PIL backend.")
        }
    }
}

fn convert_to_pil_queriable_string<F>(
    query: Queriable<F>,
    annotations_map: &HashMap<UUID, (UUID, String)>,
) -> String {
    match query {
        Queriable::Internal(s) => format!("{}", annotations_map.get(&s.uuid()).unwrap().1),
        Queriable::Forward(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone().1;
            if !rot {
                format!("{}", annotation)
            } else {
                format!("{}'", annotation)
            }
        }
        Queriable::Shared(s, rot) => {
            let annotation = annotations_map.get(&s.uuid()).unwrap().clone().1;
            if rot == 0 {
                format!("{}", annotation)
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
                format!("{}", annotation)
            } else if rot == 1 {
                format!("{}'", annotation)
            } else {
                panic!("PIL backend does not support fixed signal with rotation other than 0 or 1.")
            }
        }
        Queriable::StepTypeNext(s) => format!("{}'", annotations_map.get(&s.uuid()).unwrap().1),
        Queriable::Halo2AdviceQuery(s, rot) => {
            panic!("Halo2 native advice query not supported by PIL backend.")
        }
        Queriable::Halo2FixedQuery(s, rot) => {
            panic!("Halo2 native fixed query not supported by PIL backend.")
        }
        Queriable::_unaccessible(_) => todo!(),
    }
}
