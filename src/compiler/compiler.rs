use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use num_bigint::BigInt;

use crate::{
    field::Field,
    frontend::dsl::{
        cb::{Constraint, Typing},
        circuit, CircuitContext, StepTypeContext,
    },
    interpreter::InterpreterTraceGenerator,
    parser::{
        ast::{debug_sym_factory::DebugSymRefFactory, tl::TLDecl, Identifiable, Identifier},
        lang::TLDeclsParser,
    },
    plonkish,
    poly::{self, cse::{cse, replace_common_subexprs}, mielim::mi_elimination, reduce::reduce_degree, Expr},
    sbpir::{query::Queriable, InternalSignal, SBPIR},
    wit_gen::{NullTraceGenerator, SymbolSignalMapping, TraceGenerator},
};

use super::{
    semantic::{SymTable, SymbolCategory},
    setup_inter::{interpret, Setup},
    Config, Message, Messages,
};

/// Contains the result of a compilation.
#[derive(Debug)]
pub struct CompilerResult<F: Field + Hash> {
    pub messages: Vec<Message>,
    // pub wit_gen: WitnessGenerator,
    pub circuit: SBPIR<F, InterpreterTraceGenerator>,
}

impl<F: Field + Hash> CompilerResult<F> {
    /// Compiles to the Plonkish IR, that then can be compiled to plonkish backends.
    pub fn plonkish<
        CM: plonkish::compiler::cell_manager::CellManager,
        SSB: plonkish::compiler::step_selector::StepSelectorBuilder,
    >(
        &self,
        config: plonkish::compiler::CompilerConfig<CM, SSB>,
    ) -> (
        crate::plonkish::ir::Circuit<F>,
        Option<plonkish::ir::assignments::AssignmentGenerator<F, InterpreterTraceGenerator>>,
    ) {
        plonkish::compiler::compile(config, &self.circuit)
    }
}

/// This compiler compiles from chiquito source code to the SBPIR.
#[derive(Default)]
pub(super) struct Compiler<F> {
    pub(super) config: Config,

    messages: Vec<Message>,

    mapping: SymbolSignalMapping,

    _p: PhantomData<F>,
}

impl<F: Field + Hash> Compiler<F> {
    /// Creates a configured compiler.
    pub fn new(config: Config) -> Self {
        Compiler {
            config,
            ..Compiler::default()
        }
    }

    /// Compile the source code.
    pub(super) fn compile(
        mut self,
        source: &str,
        debug_sym_ref_factory: &DebugSymRefFactory,
    ) -> Result<CompilerResult<F>, Vec<Message>> {
        let ast = self
            .parse(source, debug_sym_ref_factory)
            .map_err(|_| self.messages.clone())?;
        let symbols = self.semantic(&ast).map_err(|_| self.messages.clone())?;
        let setup = Self::interpret(&ast, &symbols);
        let setup = Self::map_consts(setup);
        let circuit = self.build(&setup, &symbols);
        let circuit = Self::mi_elim(circuit);
        let circuit = if let Some(degree) = self.config.max_degree {
            Self::reduce(circuit, degree)
        } else {
            circuit
        };

        let circuit = self.cse(circuit);

        println!("------- After CSE -------");
        println!("{:#?}", circuit);

        let circuit =
            circuit.with_trace(InterpreterTraceGenerator::new(ast, symbols, self.mapping));

        Ok(CompilerResult {
            messages: self.messages,
            circuit,
        })
    }

    fn parse(
        &mut self,
        source: &str,
        debug_sym_ref_factory: &DebugSymRefFactory,
    ) -> Result<Vec<TLDecl<BigInt, Identifier>>, ()> {
        let result = TLDeclsParser::new().parse(debug_sym_ref_factory, source);

        match result {
            Ok(ast) => Ok(ast),
            Err(error) => {
                self.messages.push(Message::ParseErr {
                    msg: error.to_string(),
                });
                Err(())
            }
        }
    }

    fn semantic(&mut self, ast: &[TLDecl<BigInt, Identifier>]) -> Result<SymTable, ()> {
        let result = super::semantic::analyser::analyse(ast);
        let has_errors = result.messages.has_errors();

        self.messages.extend(result.messages);

        if has_errors {
            Err(())
        } else {
            Ok(result.symbols)
        }
    }

    fn interpret(
        ast: &[TLDecl<BigInt, Identifier>],
        symbols: &SymTable,
    ) -> Setup<BigInt, Identifier> {
        interpret(ast, symbols)
    }

    fn map_consts(setup: Setup<BigInt, Identifier>) -> Setup<F, Identifier> {
        setup
            .iter()
            .map(|(machine_id, machine)| {
                let new_machine: HashMap<String, Vec<Expr<F, Identifier, ()>>> = machine
                    .iter()
                    .map(|(step_id, step)| {
                        let new_step = step.iter().map(|pi| Self::map_pi_consts(pi)).collect();

                        (step_id.clone(), new_step)
                    })
                    .collect();

                (machine_id.clone(), new_machine)
            })
            .collect()
    }

    fn map_pi_consts(expr: &Expr<BigInt, Identifier, ()>) -> Expr<F, Identifier, ()> {
        use Expr::*;
        match expr {
            Const(v, _) => Const(F::from_big_int(v), ()),
            Sum(ses, _) => Sum(ses.iter().map(|se| Self::map_pi_consts(se)).collect(), ()),
            Mul(ses, _) => Mul(ses.iter().map(|se| Self::map_pi_consts(se)).collect(), ()),
            Neg(se, _) => Neg(Box::new(Self::map_pi_consts(se)), ()),
            Pow(se, exp, _) => Pow(Box::new(Self::map_pi_consts(se)), *exp, ()),
            Query(q, _) => Query(q.clone(), ()),
            Halo2Expr(_, _) => todo!(),
            MI(se, _) => MI(Box::new(Self::map_pi_consts(se)), ()),
        }
    }

    fn build(
        &mut self,
        setup: &Setup<F, Identifier>,
        symbols: &SymTable,
    ) -> SBPIR<F, NullTraceGenerator> {
        circuit::<F, (), _>("circuit", |ctx| {
            for (machine_id, machine) in setup {
                self.add_forwards(ctx, symbols, machine_id);
                self.add_step_type_handlers(ctx, symbols, machine_id);

                for state_id in machine.keys() {
                    ctx.step_type_def(
                        self.mapping.get_step_type_handler(machine_id, state_id),
                        |ctx| {
                            self.add_internals(ctx, symbols, machine_id, state_id);

                            ctx.setup(|ctx| {
                                let poly_constraints =
                                    self.translate_queries(symbols, setup, machine_id, state_id);
                                poly_constraints.iter().for_each(|poly| {
                                    let constraint = Constraint {
                                        annotation: format!("{:?}", poly),
                                        expr: poly.clone(),
                                        typing: Typing::AntiBooly,
                                    };
                                    ctx.constr(constraint);
                                });
                            });

                            ctx.wg(|_, _: ()| {})
                        },
                    );
                }
            }

            ctx.trace(|_, _| {});
        })
        .without_trace()
    }

    fn mi_elim(mut circuit: SBPIR<F, NullTraceGenerator>) -> SBPIR<F, NullTraceGenerator> {
        for (_, step_type) in circuit.step_types.iter_mut() {
            let mut signal_factory = SignalFactory::default();

            step_type.decomp_constraints(|expr| mi_elimination(expr.clone(), &mut signal_factory));
        }

        circuit
    }

    fn reduce(
        mut circuit: SBPIR<F, NullTraceGenerator>,
        degree: usize,
    ) -> SBPIR<F, NullTraceGenerator> {
        for (_, step_type) in circuit.step_types.iter_mut() {
            let mut signal_factory = SignalFactory::default();

            step_type.decomp_constraints(|expr| {
                reduce_degree(expr.clone(), degree, &mut signal_factory)
            });
        }

        circuit
    }

    fn cse(&self, mut circuit: SBPIR<F, NullTraceGenerator>) -> SBPIR<F, NullTraceGenerator> {
        let mut queriables: Vec<Queriable<F>> = Vec::new();

        self.mapping.forward_signals.iter().for_each(|(_, signal)| {
            queriables.push(Queriable::Forward(signal.clone(), false));
            queriables.push(Queriable::Forward(signal.clone(), true));
        });
        self.mapping
            .internal_signals
            .iter()
            .for_each(|(_, signal)| {
                queriables.push(Queriable::Internal(signal.clone()));
            });

        let mut signal_factory: SignalFactory<F> = SignalFactory::default();

        let mut exprs = Vec::new();
        // Take all the constraints from the circuit
        for (_, step_type) in circuit.step_types.iter_mut() {
            for constraint in &step_type.constraints {
                exprs.push(constraint.expr.clone());
            }
        }
        // get all the common subexpressions and the random assignments used in the hash
        let (common_ses, assignments) = cse(&exprs, &queriables, None);

        for (_, step_type) in circuit.step_types.iter_mut() {
            // replace the common subexpressions with the new signals
            step_type.decomp_constraints(|expr| {
                replace_common_subexprs(expr.clone(), &common_ses, &assignments, &mut signal_factory)
            })
        }

        circuit
    }

    fn translate_queries(
        &mut self,
        symbols: &SymTable,
        setup: &Setup<F, Identifier>,
        machine_id: &str,
        state_id: &str,
    ) -> Vec<Expr<F, Queriable<F>, ()>> {
        let exprs = setup.get(machine_id).unwrap().get(state_id).unwrap();

        exprs
            .iter()
            .map(|expr| self.translate_queries_expr(symbols, machine_id, state_id, expr))
            .collect()
    }

    fn translate_queries_expr(
        &mut self,
        symbols: &SymTable,
        machine_id: &str,
        state_id: &str,
        expr: &Expr<F, Identifier, ()>,
    ) -> Expr<F, Queriable<F>, ()> {
        use Expr::*;
        match expr {
            Const(v, _) => Const(*v, ()),
            Sum(ses, _) => Sum(
                ses.iter()
                    .map(|se| self.translate_queries_expr(symbols, machine_id, state_id, se))
                    .collect(),
                (),
            ),
            Mul(ses, _) => Mul(
                ses.iter()
                    .map(|se| self.translate_queries_expr(symbols, machine_id, state_id, se))
                    .collect(),
                (),
            ),
            Neg(se, _) => Neg(
                Box::new(self.translate_queries_expr(symbols, machine_id, state_id, se.as_ref())),
                (),
            ),
            Pow(se, exp, _) => Pow(
                Box::new(self.translate_queries_expr(symbols, machine_id, state_id, se.as_ref())),
                *exp,
                (),
            ),
            MI(se, _) => MI(
                Box::new(self.translate_queries_expr(symbols, machine_id, state_id, se.as_ref())),
                (),
            ),
            Halo2Expr(se, _) => Halo2Expr(se.clone(), ()),
            Query(id, _) => Query(self.translate_query(symbols, machine_id, state_id, id), ()),
        }
    }

    fn translate_query(
        &mut self,
        symbols: &SymTable,
        machine_id: &str,
        state_id: &str,
        id: &Identifier,
    ) -> Queriable<F> {
        use super::semantic::{ScopeCategory, SymbolCategory::*};

        let symbol = symbols
            .find_symbol(
                &[
                    "/".to_string(),
                    machine_id.to_string(),
                    state_id.to_string(),
                ],
                id.name(),
            )
            .unwrap_or_else(|| panic!("semantic analyser fail: undeclared id {}", id.name()));

        match symbol.symbol.category {
            InputSignal | OutputSignal | InoutSignal => {
                self.translate_forward_queriable(machine_id, id)
            }
            Signal => match symbol.scope_cat {
                ScopeCategory::Machine => self.translate_forward_queriable(machine_id, id),
                ScopeCategory::State => {
                    if id.rotation() != 0 {
                        unreachable!("semantic analyser should prevent this");
                    }
                    let signal = self
                        .mapping
                        .get_internal(&format!("//{}/{}", machine_id, state_id), &id.name());

                    Queriable::Internal(signal)
                }

                ScopeCategory::Global => unreachable!("no global signals"),
            },

            State => {
                Queriable::StepTypeNext(self.mapping.get_step_type_handler(machine_id, &id.name()))
            }

            _ => unreachable!("semantic analysis should prevent this"),
        }
    }

    fn translate_forward_queriable(&mut self, machine_id: &str, id: &Identifier) -> Queriable<F> {
        let forward = self.mapping.get_forward(machine_id, &id.name());
        let rot = if id.rotation() == 0 {
            false
        } else if id.rotation() == 1 {
            true
        } else {
            unreachable!("semantic analyser should prevent this")
        };

        Queriable::Forward(forward, rot)
    }

    fn get_all_internals(
        &mut self,
        symbols: &SymTable,
        machine_id: &str,
        state_id: &str,
    ) -> Vec<String> {
        let symbols = symbols
            .get_scope(&[
                "/".to_string(),
                machine_id.to_string(),
                state_id.to_string(),
            ])
            .expect("scope not found")
            .get_symbols();

        symbols
            .iter()
            .filter(|(_, entry)| entry.category == SymbolCategory::Signal)
            .map(|(id, _)| id)
            .cloned()
            .collect()
    }

    fn add_internals(
        &mut self,
        ctx: &mut StepTypeContext<F>,
        symbols: &SymTable,
        machine_id: &str,
        state_id: &str,
    ) {
        let internal_ids = self.get_all_internals(symbols, machine_id, state_id);
        let scope_name = format!("//{}/{}", machine_id, state_id);

        for internal_id in internal_ids {
            let name = format!("{}:{}", &scope_name, internal_id);

            let queriable = ctx.internal(name.as_str());
            if let Queriable::Internal(signal) = queriable {
                self.mapping
                    .symbol_uuid
                    .insert((scope_name.clone(), internal_id), signal.uuid());
                self.mapping.internal_signals.insert(signal.uuid(), signal);
            } else {
                unreachable!("ctx.internal returns not internal signal");
            }
        }
    }

    fn add_step_type_handlers<TG: TraceGenerator<F>>(
        &mut self,
        ctx: &mut CircuitContext<F, TG>,
        symbols: &SymTable,
        machine_id: &str,
    ) {
        let symbols = symbols
            .get_scope(&["/".to_string(), machine_id.to_string()])
            .expect("scope not found")
            .get_symbols();

        let state_ids: Vec<_> = symbols
            .iter()
            .filter(|(_, entry)| entry.category == SymbolCategory::State)
            .map(|(id, _)| id)
            .cloned()
            .collect();

        for state_id in state_ids {
            let scope_name = format!("//{}", machine_id);
            let name = format!("{}:{}", scope_name, state_id);

            let handler = ctx.step_type(&name);
            self.mapping
                .step_type_handler
                .insert(handler.uuid(), handler);
            self.mapping
                .symbol_uuid
                .insert((scope_name, state_id), handler.uuid());
        }
    }

    fn add_forwards<TG: TraceGenerator<F>>(
        &mut self,
        ctx: &mut CircuitContext<F, TG>,
        symbols: &SymTable,
        machine_id: &str,
    ) {
        let symbols = symbols
            .get_scope(&["/".to_string(), machine_id.to_string()])
            .expect("scope not found")
            .get_symbols();

        let forward_ids: Vec<_> = symbols
            .iter()
            .filter(|(_, entry)| entry.is_signal())
            .map(|(id, _)| id)
            .cloned()
            .collect();

        for forward_id in forward_ids {
            let scope_name = format!("//{}", machine_id);
            let name = format!("{}:{}", scope_name, forward_id);

            let queriable = ctx.forward(name.as_str());
            if let Queriable::Forward(signal, _) = queriable {
                self.mapping
                    .symbol_uuid
                    .insert((scope_name, forward_id), signal.uuid());
                self.mapping.forward_signals.insert(signal.uuid(), signal);
            } else {
                unreachable!("ctx.internal returns not internal signal");
            }
        }
    }
}

// Basic signal factory.
#[derive(Default)]
struct SignalFactory<F> {
    count: u64,
    _p: PhantomData<F>,
}

impl<F> poly::SignalFactory<Queriable<F>> for SignalFactory<F> {
    fn create<S: Into<String>>(&mut self, annotation: S) -> Queriable<F> {
        self.count += 1;
        Queriable::Internal(InternalSignal::new(format!(
            "{}-{}",
            annotation.into(),
            self.count
        )))
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        compiler::{compile, compile_file},
        parser::ast::debug_sym_factory::DebugSymRefFactory,
    };

    use super::Config;

    #[test]
    fn test_compiler_fibo() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get bound to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bound to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let debug_sym_ref_factory = DebugSymRefFactory::new("", circuit);
        let result = compile::<Fr>(
            circuit,
            Config::default().max_degree(2),
            &debug_sym_ref_factory,
        );

        match result {
            Ok(result) => println!("{:#?}", result),
            Err(messages) => println!("{:#?}", messages),
        }
    }

    #[test]
    fn test_compiler_fibo_file() {
        let path = "test/circuit.chiquito";
        let result = compile_file::<Fr>(path, Config::default().max_degree(2));
        assert!(result.is_ok());
    }

    #[test]
    fn test_compiler_fibo_file_err() {
        let path = "test/circuit_error.chiquito";
        let result = compile_file::<Fr>(path, Config::default().max_degree(2));

        assert!(result.is_err());

        assert_eq!(
            format!("{:?}", result.unwrap_err()),
            r#"[SemErr { msg: "use of undeclared variable c", dsym: test/circuit_error.chiquito:24:39 }, SemErr { msg: "use of undeclared variable c", dsym: test/circuit_error.chiquito:28:46 }]"#
        )
    }
}
