use std::{collections::HashMap, fmt::Debug, hash::Hash, rc::Rc};

use crate::{field::Field, sbpir::SBPIR, util::UUID, wit_gen::TraceWitness};

use super::{
    assignments::{AssignmentGenerator, Assignments},
    Circuit,
};

#[derive(Debug)]
pub struct SuperCircuit<F, MappingArgs> {
    sub_circuits: Vec<Circuit<F>>,
    mapping: MappingGenerator<F, MappingArgs>,
    sub_circuit_asts: Vec<SBPIR<F, ()>>,
}

impl<F, MappingArgs> Default for SuperCircuit<F, MappingArgs> {
    fn default() -> Self {
        Self {
            sub_circuits: Default::default(),
            mapping: Default::default(),
            sub_circuit_asts: Default::default(),
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

    // Needed for the PIL backend.
    pub fn add_sub_circuit_ast(&mut self, sub_circuit_ast: SBPIR<F, ()>) {
        self.sub_circuit_asts.push(sub_circuit_ast);
    }

    // Mapping from AST id to IR id is needed for the PIL backend to match TraceWitness, which has
    // IR id, to AST.
    pub fn get_ast_id_to_ir_id_mapping(&self) -> HashMap<UUID, UUID> {
        let mut ast_id_to_ir_id_mapping: HashMap<UUID, UUID> = HashMap::new();
        self.sub_circuits.iter().for_each(|circuit| {
            let ir_id = circuit.id;
            let ast_id = circuit.ast_id;
            ast_id_to_ir_id_mapping.insert(ast_id, ir_id);
        });
        ast_id_to_ir_id_mapping
    }
}

// Needed for the PIL backend.
impl<F: Clone, MappingArgs> SuperCircuit<F, MappingArgs> {
    pub fn get_super_asts(&self) -> Vec<SBPIR<F, ()>> {
        self.sub_circuit_asts.clone()
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
pub type SuperTraceWitness<F> = HashMap<UUID, TraceWitness<F>>;

#[derive(Clone)]
pub struct MappingContext<F> {
    assignments: SuperAssignments<F>,
    trace_witnesses: SuperTraceWitness<F>,
}

impl<F: Default> Default for MappingContext<F> {
    fn default() -> Self {
        Self {
            assignments: Default::default(),
            trace_witnesses: Default::default(),
        }
    }
}

impl<F: Field + Hash> MappingContext<F> {
    pub fn map<TraceArgs>(&mut self, gen: &AssignmentGenerator<F, TraceArgs>, args: TraceArgs) {
        let trace_witness = gen.generate_trace_witness(args);
        self.trace_witnesses
            .insert(gen.uuid(), trace_witness.clone());
        self.assignments
            .insert(gen.uuid(), gen.generate_with_witness(trace_witness));
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

    pub fn get_trace_witnesses(self) -> SuperTraceWitness<F> {
        self.trace_witnesses
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

impl<F, MappingArgs> std::fmt::Debug for MappingGenerator<F, MappingArgs> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MappingGenerator")
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

    // Needed for the PIL backend.
    pub fn generate_super_trace_witnesses(&self, args: MappingArgs) -> SuperTraceWitness<F> {
        let mut ctx = MappingContext::default();

        (self.mapping)(&mut ctx, args);

        ctx.get_trace_witnesses()
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        plonkish::{
            compiler::{cell_manager::Placement, step_selector::StepSelector},
            ir::Column,
        },
        util::uuid,
        wit_gen::{AutoTraceGenerator, TraceGenerator},
    };

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

        fn simple_circuit() -> Circuit<Fr> {
            let columns = vec![Column::advice('a', 0)];
            let exposed = vec![(Column::advice('a', 0), 2)];
            let polys = vec![];
            let lookups = vec![];
            let fixed_assignments = Default::default();

            Circuit {
                columns,
                exposed,
                polys,
                lookups,
                fixed_assignments,
                id: uuid(),
                ast_id: uuid(),
            }
        }

        let sub_circuit = simple_circuit();

        super_circuit.add_sub_circuit(sub_circuit.clone());

        assert_eq!(super_circuit.sub_circuits.len(), 1);
        assert_eq!(super_circuit.sub_circuits[0].id, sub_circuit.id);
        assert_eq!(super_circuit.sub_circuits[0].ast_id, sub_circuit.ast_id);
        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits[0].columns),
            format!("{:#?}", sub_circuit.columns)
        );
        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits[0].exposed),
            format!("{:#?}", sub_circuit.exposed)
        );
        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits[0].polys),
            format!("{:#?}", sub_circuit.polys)
        );
        assert_eq!(
            format!("{:#?}", super_circuit.sub_circuits[0].lookups),
            format!("{:#?}", sub_circuit.lookups)
        );
    }

    #[test]
    fn test_get_sub_circuits() {
        fn simple_circuit() -> Circuit<Fr> {
            let columns = vec![Column::advice('a', 0)];
            let exposed = vec![(Column::advice('a', 0), 2)];
            let polys = vec![];
            let lookups = vec![];
            let fixed_assignments = Default::default();

            Circuit {
                columns,
                exposed,
                polys,
                lookups,
                fixed_assignments,
                id: uuid(),
                ast_id: uuid(),
            }
        }

        let super_circuit: SuperCircuit<Fr, ()> = SuperCircuit {
            sub_circuits: vec![simple_circuit()],
            mapping: Default::default(),
            sub_circuit_asts: Default::default(),
        };

        let sub_circuits = super_circuit.get_sub_circuits();

        assert_eq!(sub_circuits.len(), 1);
        assert_eq!(sub_circuits[0].id, super_circuit.sub_circuits[0].id);
    }

    #[test]
    fn test_mapping_context_default() {
        let ctx = MappingContext::<Fr>::default();

        assert_eq!(
            format!("{:#?}", ctx.assignments),
            format!("{:#?}", SuperAssignments::<Fr>::default())
        );
    }

    fn simple_assignment_generator() -> AssignmentGenerator<Fr, ()> {
        AssignmentGenerator::new(
            vec![Column::advice('a', 0)],
            Placement {
                forward: HashMap::new(),
                shared: HashMap::new(),
                fixed: HashMap::new(),
                steps: HashMap::new(),
                columns: vec![],
                base_height: 0,
            },
            StepSelector::default(),
            TraceGenerator::default(),
            AutoTraceGenerator::default(),
            1,
            uuid(),
        )
    }

    #[test]
    fn test_mapping_context_map() {
        let mut ctx = MappingContext::<Fr>::default();

        assert_eq!(ctx.assignments.len(), 0);

        let gen = simple_assignment_generator();

        ctx.map(&gen, ());

        assert_eq!(ctx.assignments.len(), 1);
    }

    #[test]
    fn test_mapping_context_map_with_witness() {
        let mut ctx = MappingContext::<Fr>::default();

        let gen = simple_assignment_generator();

        let witness = TraceWitness::<Fr> {
            step_instances: vec![],
        };

        ctx.map_with_witness(&gen, witness);

        assert_eq!(ctx.assignments.len(), 1);
    }
}
