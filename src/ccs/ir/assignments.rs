use std::{
    collections::HashMap,
    hash::Hash,
    ops::{Deref, DerefMut},
};

use crate::{
    ccs::compiler::{cell_manager::Placement, step_selector::StepSelector},
    field::Field,
    sbpir::query::Queriable,
    util::UUID,
    wit_gen::{AutoTraceGenerator, StepInstance, TraceGenerator, TraceWitness},
};

pub type Coeffs<F> = Vec<Vec<Vec<Vec<(F, UUID, bool)>>>>;

// #[derive(Debug, Clone)]
// pub struct StepsID(pub Vec<UUID>);

// impl Default for StepsID {
//     fn default() -> Self {
//         Self::new()
//     }
// }

// impl StepsID {
//     pub fn new() -> Self {
//         Self(Vec::new())
//     }

//     pub fn new_with_witness<F>(witness: &TraceWitness<F>) -> Self {

//         let uuids = witness.step_instances.iter().map(|step| step.step_type_uuid).collect();
//         Self(uuids)

//     }

//     pub fn len(&self) -> usize {
//         self.0.len()
//     }

//     pub fn is_empty(&self) -> bool {
//         self.len() == 0
//     }

//     pub fn read(&self, index: usize) -> UUID {
//         assert!(index < self.len());
//         self.0[index]
//     }
// }

#[derive(Debug, Clone)]
pub struct Assignments<F>(pub Vec<(UUID, HashMap<UUID, F>)>);

impl<F> Default for Assignments<F> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<F> Deref for Assignments<F> {
    type Target = Vec<(UUID, HashMap<UUID, F>)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F> DerefMut for Assignments<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<F: Field> Assignments<F> {
    pub fn new(values: Vec<(UUID, HashMap<UUID, F>)>) -> Self {
        Self(values)
    }

    pub fn new_with_witness(witness: &TraceWitness<F>) -> Self {
        let values = witness
            .step_instances
            .iter()
            .map(|step_instance| {
                let step_id = step_instance.step_type_uuid;
                let mut values = HashMap::new();
                for (q, v) in step_instance.assignments.iter() {
                    values.insert(q.uuid(), *v);
                }
                (step_id, values)
            })
            .collect();

        Self::new(values)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn append(&mut self, ass: &mut Vec<(UUID, HashMap<UUID, F>)>) {
        self.0.append(ass)
    }

    pub fn read(&self) -> Vec<(UUID, HashMap<UUID, F>)> {
        self.0.clone()
    }

    pub fn get(&self, step_idx: usize, signal_id: UUID) -> F {
        *self.0[step_idx].1.get(&signal_id).unwrap()
    }

    pub fn write(&mut self, step_idx: usize, signal_id: UUID, value: F) {
        self.0[step_idx].1.insert(signal_id, value);
    }
}

pub struct AssignmentGenerator<F, TraceArgs> {
    placement: Placement,
    selector: StepSelector<F>,
    matrix_values: HashMap<UUID, Coeffs<F>>,
    trace_gen: TraceGenerator<F, TraceArgs>,
    auto_trace_gen: AutoTraceGenerator<F>,

    ir_id: UUID,
}

impl<F: Clone, TraceArgs> Clone for AssignmentGenerator<F, TraceArgs> {
    fn clone(&self) -> Self {
        Self {
            ir_id: self.ir_id,
            placement: self.placement.clone(),
            selector: self.selector.clone(),
            matrix_values: self.matrix_values.clone(),
            trace_gen: self.trace_gen.clone(),
            auto_trace_gen: self.auto_trace_gen.clone(),
        }
    }
}

impl<F: Clone, TraceArgs> Default for AssignmentGenerator<F, TraceArgs> {
    fn default() -> Self {
        Self {
            ir_id: Default::default(),
            placement: Default::default(),
            selector: Default::default(),
            matrix_values: Default::default(),
            trace_gen: Default::default(),
            auto_trace_gen: Default::default(),
        }
    }
}

impl<F: Field + Hash, TraceArgs> AssignmentGenerator<F, TraceArgs> {
    pub fn new(
        ir_id: UUID,
        placement: Placement,
        selector: StepSelector<F>,
        matrix_values: HashMap<UUID, Coeffs<F>>,
        trace_gen: TraceGenerator<F, TraceArgs>,
        auto_trace_gen: AutoTraceGenerator<F>,
    ) -> Self {
        Self {
            ir_id,
            placement,
            selector,
            matrix_values,
            trace_gen,
            auto_trace_gen,
        }
    }

    pub fn trace_witness(&self, args: TraceArgs) -> TraceWitness<F> {
        self.trace_gen.generate(args)
    }

    pub fn generate(&self, args: TraceArgs) -> Assignments<F> {
        let witness = self.trace_gen.generate(args);

        self.generate_with_witness(witness)
    }

    pub fn generate_with_witness(&self, witness: TraceWitness<F>) -> Assignments<F> {
        let witness = self.auto_trace_gen.generate(witness);

        let mut assignments = Assignments::new_with_witness(&witness);

        for (idx, step_instance) in witness.step_instances.iter().enumerate() {
            self.assign_step(idx, step_instance, &mut assignments);
        }

        assignments
    }

    pub fn assign_step(
        &self,
        idx: usize,
        step_instance: &StepInstance<F>,
        assignments: &mut Assignments<F>,
    ) {
        for (lhs, &rhs) in step_instance.assignments.iter() {
            let next = is_next(lhs);
            if next {
                assignments.write(idx + 1, lhs.uuid(), rhs);
            } else {
                assignments.write(idx, lhs.uuid(), rhs);
            }
        }
    }

    pub fn uuid(&self) -> UUID {
        self.ir_id
    }
}

fn is_next<F>(query: &Queriable<F>) -> bool {
    match query {
        Queriable::Forward(_, next) => *next,
        _ => false,
    }
}

pub struct PublicInputs<F>(pub Vec<F>);

impl<F> Default for PublicInputs<F> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<F: Field> PublicInputs<F> {
    pub fn new(values: Vec<F>) -> Self {
        Self(values)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
