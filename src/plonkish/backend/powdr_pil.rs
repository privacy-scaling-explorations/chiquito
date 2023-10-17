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

use crate::{
    ast::{Circuit, StepType},
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
    witness: TraceWitness<F>,
}

impl<F: Debug, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn new(ast: Circuit<F, TraceArgs>, witness: TraceWitness<F>) -> Self {
        Self { ast, witness }
    }
}

pub struct ChiquitoPilSuperCircuit<F, TraceArgs> {
    super_ast: HashMap<UUID, Circuit<F, TraceArgs>>,
    super_witness: HashMap<UUID, TraceWitness<F>>,
}

impl<F: Debug, TraceArgs> ChiquitoPilSuperCircuit<F, TraceArgs> {
    pub fn default() -> Self {
        Self {
            super_ast: HashMap::new(),
            super_witness: HashMap::new(),
        }
    }

    pub fn add(mut self: ChiquitoPilSuperCircuit<F, TraceArgs>, ast: Circuit<F, TraceArgs>, witness: TraceWitness<F>) {
        let id = ast.id;
        self.super_ast.insert(id, ast);
        self.super_witness.insert(id, witness);
    }
}

impl<F: Debug, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn to_pil(self: &ChiquitoPil<F, TraceArgs>) -> String {
        // create new string buffer
        let mut pil = String::new();
        writeln!(pil, "constant %NUM_STEPS = {};", self.ast.num_steps);
        writeln!(pil, "namespace Circuit(%NUM_STEPS);");

        // create annotation map for all signals and step types
        // categorize annotations for signals and step types in UUID vectors
        // note that internal signals defined in different step types will be duplicated
        let mut annotations_map = self.ast.annotations.clone();

        let mut col_witness_uuids: Vec<UUID> = Vec::new();
        for (_, step_type) in &self.ast.step_types {
            annotations_map.extend(step_type.annotations.clone());
            col_witness_uuids.extend::<Vec<UUID>>(
                step_type
                    .signals
                    .iter()
                    .map(|signal| signal.uuid())
                    .collect(),
            );
        }
        for annotation in annotations_map.values_mut() {
            *annotation = annotation.replace(" ", "_");
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

        assert!(
            col_witness_uuids.len() + col_fixed_uuids.len() + col_fixed_step_types_uuids.len()
                == annotations_map.len()
        );

        // declare witness columns
        if !col_witness_uuids.is_empty() {
            let mut col_witness = String::from("col witness ");
            // get unique witness annotations
            let col_witness_vars = col_witness_uuids
                .iter()
                .map(|uuid| annotations_map.get(&uuid).unwrap().clone())
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
                .map(|uuid| annotations_map.get(&uuid).unwrap().clone())
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
        for (_, step_type) in &self.ast.step_types {
            let step_type_name = annotations_map.get(&step_type.uuid()).unwrap();
            writeln!(pil, "// == step type {} start ==", step_type_name).unwrap();
            let mut step_type_selector = String::new();
            write!(step_type_selector, "col fixed {} = [", step_type_name);
            for (index, step_instance) in self.witness.step_instances.iter().enumerate() {
                if step_instance.step_type_uuid == step_type.uuid() {
                    write!(step_type_selector, "1");
                } else {
                    write!(step_type_selector, "0");
                }
                if index == self.witness.step_instances.len() - 1 {
                    write!(step_type_selector, "]");
                } else {
                    write!(step_type_selector, ", ");
                }
                // println!("step instance: {:?}", step_instance.step_type_uuid);
            }
            writeln!(pil, "{}", step_type_selector);
            let is_last_step_instance =
                step_type.uuid() == self.witness.step_instances.last().unwrap().step_type_uuid;
            writeln!(
                pil,
                "{}",
                step_type
                    .to_pil(&annotations_map, is_last_step_instance)
                    .as_str()
            );
        }

        // pragma_first_step
        if let Some(first_step) = self.ast.first_step {
            let first_step_name = annotations_map.get(&first_step).unwrap();
            writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name);
        }

        // pragma_last_step
        if let Some(last_step) = self.ast.last_step {
            let last_step_name = annotations_map.get(&last_step).unwrap();
            writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name);
        }

        pil
    }
}

impl<F: Debug> StepType<F> {
    pub fn to_pil(
        self: &StepType<F>,
        annotations_map: &HashMap<UUID, String>,
        is_last_step_instance: bool,
    ) -> String {
        let mut pil = String::new();
        let step_type_name = annotations_map.get(&self.uuid()).unwrap();
        for constraint in &self.constraints {
            let expr = convert_to_pil_rotation(&format!("{:?}", constraint.expr));

            writeln!(pil, "{} * {} = 0;", step_type_name, expr);
        }
        for transition in &self.transition_constraints {
            // apply convert_to_pil_rotation to the Debug string of transition.expr
            let expr = convert_to_pil_rotation(&format!("{:?}", transition.expr));
            // disable transition constraint in the last step instance
            if (is_last_step_instance) {
                writeln!(pil, "(1 - ISLAST) * {} * {} = 0;", step_type_name, expr);
            } else {
                writeln!(pil, "{} * {} = 0;", step_type_name, expr);
            }
        }
        pil
    }
}

fn convert_to_pil_rotation(expr: &str) -> String {
    // replace non alphanumeric characters with _ except brackets + - * / ^
    // let re = regex::Regex::new(r"[^\w\(\)+\-*/^]").unwrap();
    // let expr = re.replazce_all(expr, "_").into_owned();
    // convert rotation
    let re = regex::Regex::new(r"next\((\w+)\)").unwrap(); // w+ is alphanumeric
    re.replace_all(expr, "$1'").into_owned() // 1st capture group w+ and append with '
}
