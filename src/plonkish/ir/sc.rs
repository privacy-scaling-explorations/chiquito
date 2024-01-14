use std::{collections::HashMap, fmt::Debug, hash::Hash, rc::Rc};

use crate::{field::Field, util::UUID, wit_gen::TraceWitness};

use super::{
    assignments::{AssignmentGenerator, Assignments},
    Circuit,
};

pub struct SuperCircuit<F, MappingArgs> {
    sub_circuits: Vec<Circuit<F>>,
    mapping: MappingGenerator<F, MappingArgs>,
}

impl<F: Debug, MappingArgs: Debug> Debug for SuperCircuit<F, MappingArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SuperCircuit")
            .field("sub_circuits", &self.sub_circuits)
            .field("mapping", &self.mapping)
            .finish()
    }
}

impl<F: Debug, MappingArgs: Debug> Debug for MappingGenerator<F, MappingArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MappingGenerator")
            .field("mapping", &"Function pointer cannot be printed")
            .finish()
    }
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

impl<F: Field + Hash, MappingArgs> SuperCircuit<F, MappingArgs> {
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

#[derive(Clone)]
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

impl<F: Field + Hash> MappingContext<F> {
    pub fn map<TraceArgs>(&mut self, gen: &AssignmentGenerator<F, TraceArgs>, args: TraceArgs) {
        self.assignments.insert(gen.uuid(), gen.generate(args));
    }

    pub fn map_with_witness<TraceArgs>(
        &mut self,
        gen: &AssignmentGenerator<F, TraceArgs>,
        witness: TraceWitness<F>,
    ) {
        self.assignments
            .insert(gen.uuid(), gen.generate_with_witness(witness));
    }

    pub fn get_super_assignments(self) -> SuperAssignments<F> {
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

impl<F: Field + Hash, MappingArgs> MappingGenerator<F, MappingArgs> {
    pub fn new(mapping: Rc<Mapping<F, MappingArgs>>) -> Self {
        Self { mapping }
    }

    pub fn generate(&self, args: MappingArgs) -> SuperAssignments<F> {
        let mut ctx = MappingContext::default();

        (self.mapping)(&mut ctx, args);

        ctx.get_super_assignments()
    }
}

#[cfg(test)]
mod test {
    use halo2curves::bn256::Fr;

    use super::*;

    #[test]
    fn test_default() {
        let super_circuit: SuperCircuit<Fr, ()> = Default::default();

        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits),
            format!("{:#?}", Vec::<Circuit<Fr>>::default())
        );
        assert_eq!(
            format!("{:#?}", super_circuit.mapping),
            format!("{:#?}", MappingGenerator::<Fr, ()>::default())
        );
    }

    #[test]
    fn test_add_sub_circuit() {
        let mut super_circuit: SuperCircuit<Fr, ()> = Default::default();

        let sub_circuit = Circuit::<Fr>::default();

        super_circuit.add_sub_circuit(sub_circuit.clone());

        assert_eq!(super_circuit.sub_circuits.len(), 1);
        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits[0]),
            format!("{:#?}", sub_circuit)
        );
    }

    #[test]
    fn test_get_mapping() {
        let super_circuit: SuperCircuit<Fr, ()> = Default::default();

        let mapping = super_circuit.get_mapping();

        assert_eq!(
            format!("{:#?}", mapping),
            format!("{:#?}", MappingGenerator::<Fr, ()>::default())
        );
    }

    #[test]
    fn test_set_mapping() {
        let mut super_circuit: SuperCircuit<Fr, ()> = Default::default();

        super_circuit.set_mapping(|ctx, args| {
            // Your mapping logic here
            ctx.map(&AssignmentGenerator::<Fr, ()>::default(), args)
        });

        assert_eq!(
            format!("{:#?}", super_circuit.mapping),
            format!("{:#?}", MappingGenerator::<Fr, ()>::default())
        );
    }

    #[test]
    fn test_get_sub_circuits() {
        let super_circuit: SuperCircuit<Fr, ()> = Default::default();

        let sub_circuits = super_circuit.get_sub_circuits();

        assert_eq!(
            format!("{:#?}", sub_circuits),
            format!("{:#?}", Vec::<Circuit<Fr>>::default())
        );
    }

    #[test]
    fn test_mapping_context_default() {
        let ctx = MappingContext::<Fr>::default();

        assert_eq!(
            format!("{:#?}", ctx.assignments),
            format!("{:#?}", SuperAssignments::<Fr>::default())
        );
    }

    #[test]
    fn test_mapping_context_map() {
        let mut ctx = MappingContext::<Fr>::default();

        let gen = AssignmentGenerator::<Fr, ()>::default();

        ctx.map(&gen, ());

        assert_eq!(ctx.assignments.len(), 1);
        assert_eq!(
            format!("{:#?}", ctx.assignments[&gen.uuid()]),
            format!("{:#?}", gen.generate(()))
        );
    }

    #[test]
    fn test_mapping_context_map_with_witness() {
        let mut ctx = MappingContext::<Fr>::default();

        let gen = AssignmentGenerator::<Fr, ()>::default();

        let witness = TraceWitness::<Fr>::default();

        ctx.map_with_witness(&gen, witness.clone());

        assert_eq!(ctx.assignments.len(), 1);
        assert_eq!(
            format!("{:#?}", ctx.assignments[&gen.uuid()]),
            format!("{:#?}", gen.generate_with_witness(witness))
        );
    }
}
