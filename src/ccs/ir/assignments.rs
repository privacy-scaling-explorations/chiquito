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

pub type MatrixsCoeffs<F> = Vec<Vec<(Vec<Vec<(F, UUID, bool)>>, usize)>>;

#[derive(Debug, Clone)]
pub struct StepsID(pub Vec<UUID>);

impl Default for StepsID {
    fn default() -> Self {
        Self::new()
    }
}

impl StepsID {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn read(&self, index: usize) -> UUID {
        assert!(index < self.len());
        self.0[index]
    }
}

#[derive(Debug, Clone)]
pub struct Assignments<F>(pub Vec<HashMap<UUID, F>>);

impl<F> Default for Assignments<F> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<F> Deref for Assignments<F> {
    type Target = Vec<HashMap<UUID, F>>;

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
    pub fn new(values: Vec<HashMap<UUID, F>>) -> Self {
        Self(values)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn append(&mut self, ass: &mut Vec<HashMap<UUID, F>>) {
        self.0.append(ass)
    }

    pub fn read(&self) -> Vec<HashMap<UUID, F>> {
        self.0.clone()
    }

    pub fn get(&self, step_idx: usize, signal_id: UUID) -> F {
        *self.0[step_idx].get(&signal_id).unwrap()
    }

    pub fn write(&mut self, step_idx: usize, signal_id: UUID, value: F) {
        self.0[step_idx].insert(signal_id, value);
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

    pub fn generate(&self, args: TraceArgs) -> (Assignments<F>, StepsID) {
        let witness = self.trace_gen.generate(args);

        self.generate_with_witness(witness)
    }

    pub fn generate_with_witness(&self, witness: TraceWitness<F>) -> (Assignments<F>, StepsID) {
        let witness = self.auto_trace_gen.generate(witness);

        let values: Vec<HashMap<UUID, F>> = witness
            .step_instances
            .iter()
            .map(|step_instance| {
                let mut values = HashMap::new();
                for (q, v) in step_instance.assignments.iter() {
                    values.insert(q.uuid(), *v);
                }
                values
            })
            .collect();
        let mut assignments: Assignments<F> = Assignments::new(values);

        let mut steps_id: StepsID = StepsID::new();
        for (idx, step_instance) in witness.step_instances.iter().enumerate() {
            self.assign_step(
                idx,
                step_instance,
                &mut assignments,
                witness.step_instances.len(),
            );
            steps_id.0.push(step_instance.step_type_uuid);
        }

        (assignments, steps_id)
    }

    pub fn assign_step(
        &self,
        idx: usize,
        step_instance: &StepInstance<F>,
        assignments: &mut Assignments<F>,
        step_num: usize,
    ) {
        let step_uuid = step_instance.step_type_uuid;
        let height = self.placement.base_height + self.placement.step_height(step_uuid);

        for (lhs, &rhs) in step_instance.assignments.iter() {
            let offset = self.find_placement(step_uuid, lhs, height);
            if offset < height {
                assignments.write(idx, lhs.uuid(), rhs);
            } else if idx < step_num - 1 {
                assignments.write(idx + 1, lhs.uuid(), rhs);
            }
        }
    }

    fn find_placement(&self, step_uuid: UUID, query: &Queriable<F>, height: u32) -> u32 {
        match query {
            Queriable::Internal(signal) => {
                self.placement.internal(step_uuid, signal.uuid()).offset()
            }

            Queriable::Forward(forward, next) => {
                if *next {
                    self.placement.forward(forward.uuid()).offset() + height
                } else {
                    self.placement.forward(forward.uuid()).offset()
                }
            }
            Queriable::Shared(shared, _) => self.placement.shared(shared.uuid()).offset(),

            Queriable::Fixed(fixed, _) => self.placement.fixed(fixed.uuid()).offset(),

            _ => panic!("invalid advice assignment on queriable {:?}", query),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.ir_id
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
