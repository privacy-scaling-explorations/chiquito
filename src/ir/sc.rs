use std::{collections::HashMap, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::util::UUID;

use super::{
    assignments::{AssignmentGenerator, Assignments},
    Circuit,
};

pub struct SuperCircuit<F, MappingArgs> {
    sub_circuits: Vec<Circuit<F>>,
    mapping: MappingGenerator<F, MappingArgs>,
}

impl<F, MappingArgs> Default for SuperCircuit<F, MappingArgs> {
    fn default() -> Self {
        Self {
            sub_circuits: Default::default(),
            mapping: Default::default(),
        }
    }
}

impl<F, MappingArgs> SuperCircuit<F, MappingArgs> {
    pub fn add_sub_circuit(&mut self, sub_circuit: Circuit<F>) {
        self.sub_circuits.push(sub_circuit);
    }

    pub fn get_mapping(&self) -> MappingGenerator<F, MappingArgs> {
        self.mapping.clone()
    }
}

impl<F: Field, MappingArgs> SuperCircuit<F, MappingArgs> {
    pub fn set_mapping<M: Fn(&mut MappingContext<F>, MappingArgs) + 'static>(
        &mut self,
        mapping: M,
    ) {
        self.mapping = MappingGenerator::new(Rc::new(mapping));
    }
}

impl<F: Clone, MappingArgs> SuperCircuit<F, MappingArgs> {
    pub fn get_sub_circuits(&self) -> Vec<Circuit<F>> {
        self.sub_circuits.clone()
    }
}

pub type SuperAssignments<F> = HashMap<UUID, Assignments<F>>;

pub struct MappingContext<F> {
    assignments: SuperAssignments<F>,
}

impl<F> Default for MappingContext<F> {
    fn default() -> Self {
        Self {
            assignments: Default::default(),
        }
    }
}

impl<F: Field> MappingContext<F> {
    pub fn map<TraceArgs>(&mut self, gen: &AssignmentGenerator<F, TraceArgs>, args: TraceArgs) {
        self.assignments.insert(gen.uuid(), gen.generate(args));
    }

    fn get_super_assignments(self) -> SuperAssignments<F> {
        self.assignments
    }
}

pub type Mapping<F, MappingArgs> = dyn Fn(&mut MappingContext<F>, MappingArgs) + 'static;

pub struct MappingGenerator<F, MappingArgs> {
    mapping: Rc<Mapping<F, MappingArgs>>,
}

impl<F, MappingArgs> Clone for MappingGenerator<F, MappingArgs> {
    fn clone(&self) -> Self {
        Self {
            mapping: self.mapping.clone(),
        }
    }
}

impl<F, MappingArgs> Default for MappingGenerator<F, MappingArgs> {
    fn default() -> Self {
        Self {
            mapping: Rc::new(|_, _| {}),
        }
    }
}

impl<F: Field, MappingArgs> MappingGenerator<F, MappingArgs> {
    pub fn new(mapping: Rc<Mapping<F, MappingArgs>>) -> Self {
        Self { mapping }
    }

    pub fn generate(&self, args: MappingArgs) -> SuperAssignments<F> {
        let mut ctx = MappingContext::default();

        (self.mapping)(&mut ctx, args);

        ctx.get_super_assignments()
    }
}
