use std::hash::Hash;

use halo2_proofs::arithmetic::Field;

use crate::{
    ast::Circuit,
    compiler::{
        cell_manager::CellManager, step_selector::StepSelectorBuilder, Compiler, CompilerConfig,
    },
    ir::{
        assigments::AssigmentGenerator,
        sc::{MappingContext, SuperCircuit},
    },
};

pub struct SuperCircuitContext<F, MappingArgs> {
    sc: SuperCircuit<F, MappingArgs>,
}

impl<F, MappingArgs> Default for SuperCircuitContext<F, MappingArgs> {
    fn default() -> Self {
        Self {
            sc: Default::default(),
        }
    }
}

impl<F: Field + Hash, MappingArgs> SuperCircuitContext<F, MappingArgs> {
    pub fn add<CM: CellManager, SSB: StepSelectorBuilder, TraceArgs>(
        &mut self,
        config: CompilerConfig<CM, SSB>,
        sub_circuit: Circuit<F, TraceArgs>,
    ) -> AssigmentGenerator<F, TraceArgs> {
        let compiler = Compiler::from(config);

        let (ir, assignment) = compiler.compile(&sub_circuit);

        self.sc.add_sub_circuit(ir);

        assignment.expect("circuit without trace")
    }

    pub fn mapping<D: Fn(&mut MappingContext<F>, MappingArgs) + 'static>(&mut self, def: D) {
        self.sc.set_mapping(def);
    }
}

pub fn super_circuit<F, MappingArgs, D>(_name: &str, def: D) -> SuperCircuit<F, MappingArgs>
where
    D: Fn(&mut SuperCircuitContext<F, MappingArgs>),
{
    let mut ctx = SuperCircuitContext::<F, MappingArgs>::default();

    def(&mut ctx);

    ctx.sc
}
