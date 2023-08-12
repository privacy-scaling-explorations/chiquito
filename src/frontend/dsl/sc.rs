use std::{hash::Hash, rc::Rc};

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::Circuit,
    plonkish::{
        compiler::{
            cell_manager::CellManager, compile_phase1, compile_phase2,
            step_selector::StepSelectorBuilder, unit::CompilationUnit, CompilerConfig,
        },
        ir::{
            assignments::AssignmentGenerator,
            sc::{MappingContext, SuperCircuit},
        },
    },
};

use super::{lb::LookupTableRegistry, CircuitContext};

pub struct SuperCircuitContext<F, MappingArgs> {
    super_circuit: SuperCircuit<F, MappingArgs>,
    sub_circuit_phase1: Vec<CompilationUnit<F>>,
    tables: LookupTableRegistry<F>,
}

impl<F, MappingArgs> Default for SuperCircuitContext<F, MappingArgs> {
    fn default() -> Self {
        Self {
            super_circuit: Default::default(),
            sub_circuit_phase1: Default::default(),
            tables: LookupTableRegistry::default(),
        }
    }
}

impl<F: Field + Hash, MappingArgs> SuperCircuitContext<F, MappingArgs> {
    pub fn sub_circuit<CM: CellManager, SSB: StepSelectorBuilder, TraceArgs, Imports, Exports, D>(
        &mut self,
        config: CompilerConfig<CM, SSB>,
        sub_circuit_def: D,
        imports: Imports,
    ) -> (AssignmentGenerator<F, TraceArgs>, Exports)
    where
        D: Fn(&mut CircuitContext<F, TraceArgs>, Imports) -> Exports,
    {
        let mut sub_circuit_context = CircuitContext {
            circuit: Circuit::default(),
            tables: self.tables.clone(),
        };

        let exports = sub_circuit_def(&mut sub_circuit_context, imports);

        let sub_circuit = sub_circuit_context.circuit;

        let (unit, assignment) = compile_phase1(config, &sub_circuit);
        let assignment = assignment.unwrap_or_else(|| AssignmentGenerator::empty(unit.uuid));

        self.sub_circuit_phase1.push(unit);

        (assignment, exports)
    }

    pub fn mapping<D: Fn(&mut MappingContext<F>, MappingArgs) + 'static>(&mut self, def: D) {
        self.super_circuit.set_mapping(def);
    }

    fn compile(mut self) -> SuperCircuit<F, MappingArgs> {
        let other = Rc::new(self.sub_circuit_phase1.clone());
        // let columns = other
        // .iter()
        // .map(|unit| unit.columns.clone())
        // .collect::<Vec<Vec<ir::Column>>>()
        // .concat();

        for mut unit in self.sub_circuit_phase1 {
            unit.other_sub_circuits = Rc::clone(&other);
            // unit.columns = columns.clone();

            compile_phase2(&mut unit);

            self.super_circuit.add_sub_circuit(unit.into());
        }

        self.super_circuit
    }
}

pub fn super_circuit<F: Field + Hash, MappingArgs, D>(
    _name: &str,
    def: D,
) -> SuperCircuit<F, MappingArgs>
where
    D: Fn(&mut SuperCircuitContext<F, MappingArgs>),
{
    let mut ctx = SuperCircuitContext::<F, MappingArgs>::default();

    def(&mut ctx);

    ctx.compile()
}
