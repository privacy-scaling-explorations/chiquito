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
    wit_gen::TraceWitness, util::UUID,
};
use std::fmt::{Debug, Write};
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

impl<F: Debug, TraceArgs> ChiquitoPil<F, TraceArgs> {
    pub fn to_pil(self: &ChiquitoPil<F, TraceArgs>) -> String {
        // create annotation map for all signals and step types
        // categorize annotations for signals and step types in UUID vectors
        // note that internal signals defined in different step types will be duplicated
        let mut annotations_map = self.ast.annotations.clone();
        
        let mut col_witness_uuids: Vec<UUID> = Vec::new();
        for (_, step_type) in &self.ast.step_types {
            annotations_map.extend(step_type.annotations.clone());
            col_witness_uuids.extend::<Vec<UUID>>(step_type.signals.iter().map(|signal| signal.uuid()).collect());
        }
        for annotation in annotations_map.values_mut() {
            *annotation = annotation.replace(" ", "_");
        }

        col_witness_uuids.extend::<Vec<UUID>>(self.ast.forward_signals.iter().map(|forward_signal| forward_signal.uuid()).collect());
        col_witness_uuids.extend::<Vec<UUID>>(self.ast.shared_signals.iter().map(|forward_signal| forward_signal.uuid()).collect());

        let mut col_fixed_uuids = self.ast.fixed_signals.iter().map(|fixed_signal| fixed_signal.uuid()).collect::<Vec<UUID>>();
        let mut col_fixed_step_types_uuids: Vec<UUID> = self.ast.step_types.keys().cloned().collect();

        assert!(col_witness_uuids.len() + col_fixed_uuids.len() + col_fixed_step_types_uuids.len() == annotations_map.len());

        // declare witness columns
        if !col_witness_uuids.is_empty() {
            let mut col_witness = String::from("col witness ");
            // get unique witness annotations
            col_witness_uuids.iter().map(|uuid| annotations_map.get(&uuid).unwrap().clone()).collect::<Vec<String>>();

        }


        // declare non-step type fixed columns

        // let mut col_witness = String::from("col witness ");
        // for (_, step_type) in &self.ast.step_types {
        //     for signal in &step_type.signals {
        //         let annotation = annotations_map.get(&signal.uuid).unwrap();
        //         if signal.is_fixed {
        //             writeln!(col_witness, "col fixed {} = {}", signal_name, annotation);
        //         } else {
        //             writeln!(col_witness, "col witness {} = {}", signal_name, annotation);
        //         }
        //     }
        // }

        // let mut col_fixed = String::new();
        // let mut col_fixed_step_types = String::new();

        // create new string buffer
        let mut pil = String::new();
        writeln!(pil, "constant %NUM_STEPS = {};", self.ast.num_steps);
        writeln!(pil, "namespace Circuit(%NUM_STEPS);");

        // create fixed columns for step instance selections
        // first, generate empty vectors for each step type
        // for step_type in &self.ast.step_types {

        // }

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
            let step_type_name = step_type.name.replace(" ", "_");
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
            writeln!(pil, "{}", step_type.to_pil().as_str());
        }

        // pragma_first_step
        if let Some(first_step) = self.ast.first_step {
            let first_step_name = self
                .ast
                .annotations
                .get(&first_step)
                .unwrap()
                .replace(" ", "_");
            writeln!(pil, "ISFIRST * (1 - {}) = 0", first_step_name);
        }

        // pragma_last_step
        if let Some(last_step) = self.ast.last_step {
            let last_step_name = self
                .ast
                .annotations
                .get(&last_step)
                .unwrap()
                .replace(" ", "_");
            writeln!(pil, "ISLAST * (1 - {}) = 0", last_step_name);
        }

        pil
    }
}

// impl<F: Debug, TraceArgs> Circuit<F, TraceArgs> {

// }

impl<F: Debug> StepType<F> {
    pub fn to_pil(self: &StepType<F>) -> String {
        let mut pil = String::new();
        let step_type_name = &self.name.replace(" ", "_");
        for constraint in &self.constraints {
            let expr = convert_to_pil_rotation(&format!("{:?}", constraint.expr));

            writeln!(pil, "{} * {} = 0", step_type_name, expr);
        }
        for transition in &self.transition_constraints {
            // apply convert_to_pil_rotation to the Debug string of transition.expr
            let expr = convert_to_pil_rotation(&format!("{:?}", transition.expr));

            writeln!(pil, "{} * {} = 0", step_type_name, expr);
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
