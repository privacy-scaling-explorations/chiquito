use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::Circuit as astCircuit,
    field::Field,
    util::UUID,
    wit_gen::{Trace, TraceWitness},
};

use super::{
    assignments::{AssignmentGenerator, Assignments},
    Circuit,
};

pub struct SuperCircuit<F, MappingArgs> {
    sub_circuits: Vec<Circuit<F>>,
    mapping: MappingGenerator<F, MappingArgs>,
    sub_circuit_asts: HashMap<UUID, astCircuit<F, ()>>,
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

    pub fn add_sub_circuit_ast(&mut self, sub_circuit_ast: astCircuit<F, ()>) {
        self.sub_circuit_asts
            .insert(sub_circuit_ast.id, sub_circuit_ast);
    }

    pub fn get_ast_id_to_ir_id_mapping(&self) -> HashMap<UUID, UUID> {
        // loop over sub_cicuits: Vec<Circuit> and obtain the id & ast_id of each Circuit to create
        // a HashMap
        let mut ast_id_to_ir_id_mapping: HashMap<UUID, UUID> = HashMap::new();
        self.sub_circuits.iter().for_each(|circuit| {
            let ir_id = circuit.id;
            let ast_id = circuit.ast_id;
            // insert the id & ast_id into the HashMap
            ast_id_to_ir_id_mapping.insert(ast_id, ir_id);
        });
        ast_id_to_ir_id_mapping
    }
}

impl<F: Clone, MappingArgs> SuperCircuit<F, MappingArgs> {
    pub fn get_super_asts(&self) -> HashMap<UUID, astCircuit<F, ()>> {
        self.sub_circuit_asts.clone()
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
pub type SuperTraceWitness<F> = HashMap<UUID, TraceWitness<F>>;

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

impl<F: Field> MappingContext<F> {
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

    pub fn generate_super_trace_witnesses(&self, args: MappingArgs) -> SuperTraceWitness<F> {
        let mut ctx = MappingContext::default();

        (self.mapping)(&mut ctx, args);

        ctx.get_trace_witnesses()
    }
}
