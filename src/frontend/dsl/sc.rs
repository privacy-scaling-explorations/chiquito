use std::{hash::Hash, rc::Rc};

use crate::field::Field;

use crate::{
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
    sbpir::SBPIRLegacy,
    wit_gen::{NullTraceGenerator, TraceGenerator},
};

use super::{lb::LookupTableRegistry, trace::DSLTraceGenerator, CircuitContextLegacy};

pub struct SuperCircuitContext<F, MappingArgs> {
    super_circuit: SuperCircuit<F, MappingArgs>,
    sub_circuit_phase1: Vec<CompilationUnit<F>>,
    pub tables: LookupTableRegistry<F>,
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

impl<F: Clone, MappingArgs> SuperCircuitContext<F, MappingArgs> {
    fn add_sub_circuit_ast(&mut self, ast: SBPIRLegacy<F, NullTraceGenerator>) {
        self.super_circuit.add_sub_circuit_ast(ast);
    }
}

impl<F: Field + Hash, MappingArgs> SuperCircuitContext<F, MappingArgs> {
    /// Add a sub-circuit to the super-circuit
    /// A sub-circuit is a regular circuit that is a part of a larger `SuperCircuit`
    pub fn sub_circuit<
        CM: CellManager,
        SSB: StepSelectorBuilder,
        TraceArgs: Clone,
        Imports,
        Exports,
        D,
    >(
        &mut self,
        config: CompilerConfig<CM, SSB>,
        sub_circuit_def: D,
        imports: Imports,
    ) -> (
        AssignmentGenerator<F, DSLTraceGenerator<F, TraceArgs>>,
        Exports,
    )
    where
        D: Fn(&mut CircuitContextLegacy<F, DSLTraceGenerator<F, TraceArgs>>, Imports) -> Exports,
    {
        let mut sub_circuit_context = CircuitContextLegacy {
            circuit: SBPIRLegacy::default(),
            tables: self.tables.clone(),
        };
        let exports = sub_circuit_def(&mut sub_circuit_context, imports);

        let sub_circuit = sub_circuit_context.circuit;

        // ast is used for PIL backend
        self.add_sub_circuit_ast(sub_circuit.clone_without_trace());

        let (unit, assignment) = compile_phase1(config, &sub_circuit);
        let assignment = assignment.unwrap_or_else(|| AssignmentGenerator::empty(unit.uuid));

        self.sub_circuit_phase1.push(unit);

        (assignment, exports)
    }

    /// Add a sub-circuit to the super-circuit
    /// A sub-circuit is a regular circuit that is a part of a larger `SuperCircuit`
    /// This function takes an already generated AST as input
    pub fn sub_circuit_with_ast<
        CM: CellManager,
        SSB: StepSelectorBuilder,
        TG: TraceGenerator<F> + Clone + Default,
    >(
        &mut self,
        config: CompilerConfig<CM, SSB>,
        sub_circuit: SBPIRLegacy<F, TG>, // directly input ast
    ) -> AssignmentGenerator<F, TG> {
        let (unit, assignment) = compile_phase1(config, &sub_circuit);
        let assignment = assignment.unwrap_or_else(|| AssignmentGenerator::empty(unit.uuid));

        self.sub_circuit_phase1.push(unit);

        assignment
    }

    pub fn mapping<D: Fn(&mut MappingContext<F>, MappingArgs) + 'static>(&mut self, def: D) {
        self.super_circuit.set_mapping(def);
    }

    pub fn compile(mut self) -> SuperCircuit<F, MappingArgs> {
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

/// Create a super-circuit
/// A super-circuit is a circuit that contains multiple sub-circuits
pub fn super_circuit<F: Field + Hash, MappingArgs, D, TG: TraceGenerator<F> + Clone + Default>(
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

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::{bn256::Fr, ff::PrimeField};

    use crate::{
        frontend::dsl::circuit_legacy,
        plonkish::compiler::{
            cell_manager::SingleRowCellManager, config, step_selector::SimpleStepSelectorBuilder,
        },
        poly::ToField,
    };

    use super::*;

    #[test]
    fn test_super_circuit_context_default() {
        let ctx = SuperCircuitContext::<Fr, ()>::default();

        assert_eq!(
            format!("{:#?}", ctx.super_circuit),
            format!("{:#?}", SuperCircuit::<Fr, ()>::default())
        );
        assert_eq!(
            format!("{:#?}", ctx.sub_circuit_phase1),
            format!("{:#?}", Vec::<CompilationUnit<Fr>>::default())
        );
        assert_eq!(ctx.sub_circuit_phase1.len(), 0);
        assert_eq!(
            format!("{:#?}", ctx.tables),
            format!("{:#?}", LookupTableRegistry::<Fr>::default())
        );
    }

    #[test]
    fn test_super_circuit_context_sub_circuit() {
        let mut ctx = SuperCircuitContext::<Fr, ()>::default();

        fn simple_circuit<F: PrimeField + Eq + Hash>(
            ctx: &mut CircuitContextLegacy<F, DSLTraceGenerator<F>>,
            _: (),
        ) {
            use crate::frontend::dsl::cb::*;

            let x = ctx.forward("x");
            let y = ctx.forward("y");

            let step_type = ctx.step_type_def("sum should be 10", |ctx| {
                ctx.setup(move |ctx| {
                    ctx.constr(eq(x + y, 10));
                });

                ctx.wg(move |ctx, (x_value, y_value): (u32, u32)| {
                    ctx.assign(x, x_value.field());
                    ctx.assign(y, y_value.field());
                })
            });

            ctx.pragma_num_steps(1);

            ctx.trace(move |ctx, ()| {
                ctx.add(&step_type, (2, 8));
            })
        }

        // simple circuit to check if the sum of two inputs are 10
        ctx.sub_circuit(
            config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
            simple_circuit,
            (),
        );

        // ensure phase 1 was done correctly for the sub circuit
        assert_eq!(ctx.sub_circuit_phase1.len(), 1);
        assert_eq!(ctx.sub_circuit_phase1[0].columns.len(), 4);
        assert_eq!(
            ctx.sub_circuit_phase1[0].columns[0].annotation,
            "srcm forward x"
        );
        assert_eq!(
            ctx.sub_circuit_phase1[0].columns[1].annotation,
            "srcm forward y"
        );
        assert_eq!(ctx.sub_circuit_phase1[0].columns[2].annotation, "q_enable");
        assert_eq!(
            ctx.sub_circuit_phase1[0].columns[3].annotation,
            "'step selector for sum should be 10'"
        );
        assert_eq!(ctx.sub_circuit_phase1[0].forward_signals.len(), 2);
        assert_eq!(ctx.sub_circuit_phase1[0].step_types.len(), 1);
        assert_eq!(ctx.sub_circuit_phase1[0].compilation_phase, 1);
    }

    #[test]
    fn test_super_circuit_compile() {
        let mut ctx = SuperCircuitContext::<Fr, ()>::default();

        fn simple_circuit<F: PrimeField + Eq + Hash>(
            ctx: &mut CircuitContextLegacy<F, DSLTraceGenerator<F>>,
            _: (),
        ) {
            use crate::frontend::dsl::cb::*;

            let x = ctx.forward("x");
            let y = ctx.forward("y");

            let step_type = ctx.step_type_def("sum should be 10", |ctx| {
                ctx.setup(move |ctx| {
                    ctx.constr(eq(x + y, 10));
                });

                ctx.wg(move |ctx, (x_value, y_value): (u32, u32)| {
                    ctx.assign(x, x_value.field());
                    ctx.assign(y, y_value.field());
                })
            });

            ctx.pragma_num_steps(1);

            ctx.trace(move |ctx, ()| {
                ctx.add(&step_type, (2, 8));
            })
        }

        // simple circuit to check if the sum of two inputs are 10
        ctx.sub_circuit(
            config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
            simple_circuit,
            (),
        );

        let super_circuit = ctx.compile();

        assert_eq!(super_circuit.get_sub_circuits().len(), 1);
        assert_eq!(super_circuit.get_sub_circuits()[0].columns.len(), 4);
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[0].annotation,
            "srcm forward x"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[1].annotation,
            "srcm forward y"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[2].annotation,
            "q_enable"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[3].annotation,
            "'step selector for sum should be 10'"
        );
    }

    #[test]
    fn test_super_circuit_sub_circuit_with_ast() {
        let mut ctx = SuperCircuitContext::<Fr, ()>::default();

        let simple_circuit_with_ast = circuit_legacy("simple circuit", |ctx| {
            use crate::frontend::dsl::cb::*;

            let x = ctx.forward("x");
            let y = ctx.forward("y");

            let step_type = ctx.step_type_def("sum should be 10", |ctx| {
                ctx.setup(move |ctx| {
                    ctx.constr(eq(x + y, 10));
                });

                ctx.wg(move |ctx, (x_value, y_value): (u32, u32)| {
                    ctx.assign(x, x_value.field());
                    ctx.assign(y, y_value.field());
                })
            });

            ctx.pragma_num_steps(1);

            ctx.trace(move |ctx, ()| {
                ctx.add(&step_type, (2, 8));
            });
        });

        ctx.sub_circuit_with_ast::<SingleRowCellManager, SimpleStepSelectorBuilder, DSLTraceGenerator<Fr>>(
            config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
            simple_circuit_with_ast,
        );

        let super_circuit = ctx.compile();

        assert_eq!(super_circuit.get_sub_circuits().len(), 1);
        assert_eq!(super_circuit.get_sub_circuits()[0].columns.len(), 4);
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[0].annotation,
            "srcm forward x"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[1].annotation,
            "srcm forward y"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[2].annotation,
            "q_enable"
        );
        assert_eq!(
            super_circuit.get_sub_circuits()[0].columns[3].annotation,
            "'step selector for sum should be 10'"
        );
    }
}
