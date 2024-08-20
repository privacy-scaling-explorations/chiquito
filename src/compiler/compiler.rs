use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use num_bigint::BigInt;

use crate::{
    field::Field,
    frontend::dsl::StepTypeHandler,
    interpreter::InterpreterTraceGenerator,
    parser::{
        ast::{
            debug_sym_factory::DebugSymRefFactory,
            expression::Expression,
            statement::{Statement, TypedIdDecl},
            tl::TLDecl,
            DebugSymRef, Identifiable, Identifier,
        },
        lang::TLDeclsParser,
    },
    poly::Expr,
    sbpir::{query::Queriable, sbpir_machine::SBPIRMachine, Constraint, StepType, SBPIR},
    wit_gen::{NullTraceGenerator, SymbolSignalMapping},
};

use super::{
    semantic::{SymTable, SymbolCategory},
    setup_inter::{interpret, Setup},
    Config, Message, Messages,
};

#[derive(Debug)]
pub struct CompilerResult<F: Field + Hash> {
    pub messages: Vec<Message>,
    pub circuit: SBPIR<F, InterpreterTraceGenerator>,
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
    pub fn new(mut config: Config) -> Self {
        if config.max_steps == 0 {
            config.max_steps = 1000; // TODO: organise this better
        }
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
        let ast = self.add_virtual(ast);
        let symbols = self.semantic(&ast).map_err(|_| self.messages.clone())?;
        let machine_setups = Self::interpret(&ast, &symbols);
        let machine_setups = machine_setups
            .iter()
            .map(|(k, v)| (k.clone(), v.map_consts()))
            .collect();

        let circuit = self.build(&machine_setups, &symbols);
        let circuit = circuit.eliminate_mul_inv();
        let circuit = if let Some(degree) = self.config.max_degree {
            circuit.reduce(degree)
        } else {
            circuit
        };

        let circuit = circuit.with_trace(&InterpreterTraceGenerator::new(
            ast,
            symbols,
            self.mapping,
            self.config.max_steps,
        ));

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

    /// Adds "virtual" states to the AST (necessary to handle padding)
    fn add_virtual(
        &mut self,
        mut ast: Vec<TLDecl<BigInt, Identifier>>,
    ) -> Vec<TLDecl<BigInt, Identifier>> {
        for tldc in ast.iter_mut() {
            match tldc {
                TLDecl::MachineDecl {
                    dsym,
                    id: _,
                    input_params: _,
                    output_params,
                    block,
                } => self.add_virtual_to_machine(dsym, output_params, block),
            }
        }

        ast
    }

    fn add_virtual_to_machine(
        &mut self,
        dsym: &DebugSymRef,
        output_params: &Vec<Statement<BigInt, Identifier>>,
        block: &mut Statement<BigInt, Identifier>,
    ) {
        let dsym = DebugSymRef::into_virtual(dsym);
        let output_params = Self::get_decls(output_params);

        if let Statement::Block(_, stmts) = block {
            let mut has_final = false;

            for stmt in stmts.iter() {
                if let Statement::StateDecl(_, id, _) = stmt
                    && id.name() == "final"
                {
                    has_final = true
                }
            }
            if !has_final {
                stmts.push(Statement::StateDecl(
                    dsym.clone(),
                    Identifier::new("final", dsym.clone()),
                    Box::new(Statement::Block(dsym.clone(), vec![])),
                ));
            }

            let final_state = Self::find_state_mut("final", stmts).unwrap();

            let mut padding_transitions = output_params
                .iter()
                .map(|output_signal| {
                    Statement::SignalAssignmentAssert(
                        dsym.clone(),
                        vec![output_signal.id.next()],
                        vec![Expression::Query::<BigInt, Identifier>(
                            dsym.clone(),
                            output_signal.id.clone(),
                        )],
                    )
                })
                .collect::<Vec<_>>();

            padding_transitions.push(Statement::Transition(
                dsym.clone(),
                Identifier::new("__padding", dsym.clone()),
                Box::new(Statement::Block(dsym.clone(), vec![])),
            ));

            Self::add_virtual_to_state(final_state, padding_transitions.clone());

            stmts.push(Statement::StateDecl(
                dsym.clone(),
                Identifier::new("__padding", dsym.clone()),
                Box::new(Statement::Block(dsym.clone(), padding_transitions)),
            ));
        } // Semantic analyser must show an error in the else case
    }

    fn find_state_mut<S: Into<String>>(
        state_id: S,
        stmts: &mut [Statement<BigInt, Identifier>],
    ) -> Option<&mut Statement<BigInt, Identifier>> {
        let state_id = state_id.into();
        let mut final_state: Option<&mut Statement<BigInt, Identifier>> = None;

        for stmt in stmts.iter_mut() {
            if let Statement::StateDecl(_, id, _) = stmt
                && id.name() == state_id
            {
                final_state = Some(stmt)
            }
        }

        final_state
    }

    fn add_virtual_to_state(
        state: &mut Statement<BigInt, Identifier>,
        add_statements: Vec<Statement<BigInt, Identifier>>,
    ) {
        if let Statement::StateDecl(_, _, final_state_stmts) = state {
            if let Statement::Block(_, stmts) = final_state_stmts.as_mut() {
                stmts.extend(add_statements)
            }
        }
    }

    /// Semantic analysis of the AST
    /// Returns the symbol table if successful
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

    fn interpret(ast: &[TLDecl<BigInt, Identifier>], symbols: &SymTable) -> Setup<BigInt> {
        interpret(ast, symbols)
    }

    fn build(&mut self, setup: &Setup<F>, symbols: &SymTable) -> SBPIR<F, NullTraceGenerator> {
        let mut sbpir = SBPIR::default();

        for (machine_name, machine_setup) in setup {
            let mut sbpir_machine = SBPIRMachine::default();
            self.add_forward_signals(&mut sbpir_machine, symbols, machine_name);
            self.add_step_type_handlers(&mut sbpir_machine, symbols, machine_name);

            sbpir_machine.num_steps = self.config.max_steps;
            sbpir_machine.first_step = Some(
                self.mapping
                    .get_step_type_handler(machine_name, "initial")
                    .uuid(),
            );
            sbpir_machine.last_step = Some(
                self.mapping
                    .get_step_type_handler(machine_name, "__padding")
                    .uuid(),
            );

            for state_id in machine_setup.states() {
                let handler = self.mapping.get_step_type_handler(machine_name, state_id);

                let mut step_type = StepType::new(handler.uuid(), handler.annotation.to_string());

                self.add_internal_signals(symbols, machine_name, &mut step_type, state_id);

                let poly_constraints =
                    self.translate_queries(symbols, setup, machine_name, state_id);
                poly_constraints.iter().for_each(|poly| {
                    let constraint = Constraint {
                        annotation: format!("{:?}", poly),
                        expr: poly.clone(),
                    };

                    step_type.constraints.push(constraint)
                });

                sbpir_machine.add_step_type_def(step_type);
            }

            sbpir.machines.insert(machine_name.clone(), sbpir_machine);
        }

        sbpir.without_trace()
    }

    #[allow(dead_code)]
    fn cse(mut _circuit: SBPIR<F, NullTraceGenerator>) -> SBPIR<F, NullTraceGenerator> {
        todo!()
    }

    fn translate_queries(
        &mut self,
        symbols: &SymTable,
        setup: &Setup<F>,
        machine_name: &str,
        state_id: &str,
    ) -> Vec<Expr<F, Queriable<F>, ()>> {
        let exprs = setup
            .get(machine_name)
            .unwrap()
            .get_poly_constraints(state_id)
            .unwrap();

        exprs
            .iter()
            .map(|expr| self.translate_queries_expr(symbols, machine_name, state_id, expr))
            .collect()
    }

    fn translate_queries_expr(
        &mut self,
        symbols: &SymTable,
        machine_name: &str,
        state_id: &str,
        expr: &Expr<F, Identifier, ()>,
    ) -> Expr<F, Queriable<F>, ()> {
        use Expr::*;
        match expr {
            Const(v, _) => Const(*v, ()),
            Sum(ses, _) => Sum(
                ses.iter()
                    .map(|se| self.translate_queries_expr(symbols, machine_name, state_id, se))
                    .collect(),
                (),
            ),
            Mul(ses, _) => Mul(
                ses.iter()
                    .map(|se| self.translate_queries_expr(symbols, machine_name, state_id, se))
                    .collect(),
                (),
            ),
            Neg(se, _) => Neg(
                Box::new(self.translate_queries_expr(symbols, machine_name, state_id, se.as_ref())),
                (),
            ),
            Pow(se, exp, _) => Pow(
                Box::new(self.translate_queries_expr(symbols, machine_name, state_id, se.as_ref())),
                *exp,
                (),
            ),
            MI(se, _) => MI(
                Box::new(self.translate_queries_expr(symbols, machine_name, state_id, se.as_ref())),
                (),
            ),
            Halo2Expr(se, _) => Halo2Expr(se.clone(), ()),
            Query(id, _) => Query(
                self.translate_query(symbols, machine_name, state_id, id),
                (),
            ),
        }
    }

    fn translate_query(
        &mut self,
        symbols: &SymTable,
        machine_name: &str,
        state_id: &str,
        id: &Identifier,
    ) -> Queriable<F> {
        use super::semantic::{ScopeCategory, SymbolCategory::*};

        let symbol = symbols
            .find_symbol(
                &[
                    "/".to_string(),
                    machine_name.to_string(),
                    state_id.to_string(),
                ],
                id.name(),
            )
            .unwrap_or_else(|| panic!("semantic analyser fail: undeclared id {}", id.name()));

        match symbol.symbol.category {
            InputSignal | OutputSignal | InoutSignal => {
                self.translate_forward_queriable(machine_name, id)
            }
            Signal => match symbol.scope_cat {
                ScopeCategory::Machine => self.translate_forward_queriable(machine_name, id),
                ScopeCategory::State => {
                    if id.rotation() != 0 {
                        unreachable!("semantic analyser should prevent this");
                    }
                    let signal = self
                        .mapping
                        .get_internal(&format!("//{}/{}", machine_name, state_id), &id.name());

                    Queriable::Internal(signal)
                }

                ScopeCategory::Global => unreachable!("no global signals"),
            },

            State => Queriable::StepTypeNext(
                self.mapping.get_step_type_handler(machine_name, &id.name()),
            ),

            _ => unreachable!("semantic analysis should prevent this"),
        }
    }

    fn translate_forward_queriable(&mut self, machine_name: &str, id: &Identifier) -> Queriable<F> {
        let forward = self.mapping.get_forward(machine_name, &id.name());
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
        machine_name: &str,
        state_id: &str,
    ) -> Vec<String> {
        let symbols = symbols
            .get_scope(&[
                "/".to_string(),
                machine_name.to_string(),
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

    fn add_internal_signals(
        &mut self,
        symbols: &SymTable,
        machine_name: &str,
        step_type: &mut StepType<F>,
        state_id: &str,
    ) {
        let internal_ids = self.get_all_internals(symbols, machine_name, state_id);
        let scope_name = format!("//{}/{}", machine_name, state_id);

        for internal_id in internal_ids {
            let name = format!("{}:{}", &scope_name, internal_id);
            let signal = step_type.add_signal(name.as_str());

            self.mapping
                .symbol_uuid
                .insert((scope_name.clone(), internal_id), signal.uuid());
            self.mapping.internal_signals.insert(signal.uuid(), signal);
        }
    }

    fn add_step_type_handlers(
        &mut self,
        machine: &mut SBPIRMachine<F>,
        symbols: &SymTable,
        machine_name: &str,
    ) {
        let symbols = get_symbols(symbols, machine_name);

        let state_ids: Vec<_> = symbols
            .iter()
            .filter(|(_, entry)| entry.category == SymbolCategory::State)
            .map(|(id, _)| id)
            .cloned()
            .collect();

        for state_id in state_ids {
            let scope_name = format!("//{}", machine_name);
            let name = format!("{}:{}", scope_name, state_id);

            let handler = StepTypeHandler::new(name.to_string());

            machine.add_step_type(handler, name);

            self.mapping
                .step_type_handler
                .insert(handler.uuid(), handler);
            self.mapping
                .symbol_uuid
                .insert((scope_name, state_id), handler.uuid());
        }
    }

    fn add_forward_signals(
        &mut self,
        machine: &mut SBPIRMachine<F>,
        symbols: &SymTable,
        machine_name: &str,
    ) {
        let symbols = get_symbols(symbols, machine_name);

        let forward_ids: Vec<_> = symbols
            .iter()
            .filter(|(_, entry)| entry.is_signal())
            .map(|(id, _)| id)
            .cloned()
            .collect();

        for forward_id in forward_ids {
            let scope_name = format!("//{}", machine_name);
            let name = format!("{}:{}", scope_name, forward_id);
            let queriable = Queriable::<F>::Forward(machine.add_forward(name.as_str(), 0), false);
            if let Queriable::Forward(signal, _) = queriable {
                self.mapping
                    .symbol_uuid
                    .insert((scope_name, forward_id), signal.uuid());
                self.mapping.forward_signals.insert(signal.uuid(), signal);
            } else {
                unreachable!("Forward queriable should return a forward signal");
            }
        }
    }

    fn get_decls(stmts: &Vec<Statement<BigInt, Identifier>>) -> Vec<TypedIdDecl<Identifier>> {
        let mut result: Vec<TypedIdDecl<Identifier>> = vec![];

        for stmt in stmts {
            if let Statement::SignalDecl(_, ids) = stmt {
                result.extend(ids.clone())
            }
        }

        result
    }
}

fn get_symbols<'a>(
    symbols: &'a SymTable,
    machine_name: &'a str,
) -> &'a HashMap<String, super::semantic::SymTableEntry> {
    let symbols = symbols
        .get_scope(&["/".to_string(), machine_name.to_string()])
        .expect("scope not found")
        .get_symbols();
    symbols
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use halo2_proofs::halo2curves::bn256::Fr;
    use itertools::Itertools;

    use crate::{
        compiler::{compile, compile_legacy},
        parser::ast::debug_sym_factory::DebugSymRefFactory,
        wit_gen::TraceGenerator,
    };

    use super::Config;

    // TODO rewrite the test after machines are able to call other machines
    #[test]
    fn test_compiler_fibo_multiple_machines() {
        // Source code containing two machines
        let circuit = "
        machine fibo1 (signal n) (signal b: field) {
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
              i', a', b', n' <== i + 1, b, c, n;
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
           machine fibo2 (signal n) (signal b: field) {
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
              i', a', b', n' <== i + 1, b, c, n;
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
            Ok(result) => {
                assert_eq!(result.circuit.machines.len(), 2);
                println!("{:#?}", result)
            }
            Err(messages) => println!("{:#?}", messages),
        }
    }

    #[test]
    fn test_is_new_compiler_identical_to_legacy() {
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
              i', a', b', n' <== i + 1, b, c, n;
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
        )
        .unwrap();

        let result_legacy = compile_legacy::<Fr>(
            circuit,
            Config::default().max_degree(2),
            &debug_sym_ref_factory,
        )
        .unwrap();

        let result = result.circuit.machines.get("fibo").unwrap();
        let result_legacy = result_legacy.circuit;
        let exposed = &result.exposed;
        let exposed_legacy = result_legacy.exposed;

        for exposed in exposed.iter().zip(exposed_legacy.iter()) {
            assert_eq!(exposed.0 .0, exposed.1 .0);
            assert_eq!(exposed.0 .1, exposed.1 .1);
        }
        assert_eq!(result.annotations.len(), result_legacy.annotations.len());
        for val in result_legacy.annotations.values() {
            assert!(result.annotations.values().contains(val));
        }

        assert_eq!(
            result.forward_signals.len(),
            result_legacy.forward_signals.len()
        );
        for val in result_legacy.forward_signals.iter() {
            assert!(result
                .forward_signals
                .iter()
                .any(|x| x.annotation() == val.annotation() && x.phase() == val.phase()));
        }

        assert_eq!(result.shared_signals, result_legacy.shared_signals);
        assert_eq!(result.fixed_signals, result_legacy.fixed_signals);
        assert_eq!(result.halo2_advice, result_legacy.halo2_advice);
        assert_eq!(result.halo2_fixed, result_legacy.halo2_fixed);
        assert_eq!(result.step_types.len(), result_legacy.step_types.len());
        for step in result_legacy.step_types.values() {
            let name = step.name();
            let step_new = result
                .step_types
                .iter()
                .find(|x| x.1.name() == name)
                .unwrap()
                .1;
            assert_eq!(step_new.signals.len(), step.signals.len());
            for signal in step.signals.iter() {
                assert!(step_new
                    .signals
                    .iter()
                    .any(|x| x.annotation() == signal.annotation()));
            }
            assert_eq!(step_new.constraints.len(), step.constraints.len());
            for constraint in step.constraints.iter() {
                assert!(step_new
                    .constraints
                    .iter()
                    .any(|x| x.annotation == constraint.annotation));
            }
            assert_eq!(step_new.lookups.is_empty(), step.lookups.is_empty());
            assert_eq!(
                step_new.auto_signals.is_empty(),
                step.auto_signals.is_empty()
            );
            assert_eq!(
                step_new.transition_constraints.is_empty(),
                step.transition_constraints.is_empty()
            );
            assert_eq!(step_new.annotations.len(), step.annotations.len());
        }

        assert_eq!(
            result.first_step.is_some(),
            result_legacy.first_step.is_some()
        );
        assert_eq!(
            result.last_step.is_some(),
            result_legacy.last_step.is_some()
        );
        assert_eq!(result.num_steps, result_legacy.num_steps);
        assert_eq!(result.q_enable, result_legacy.q_enable);

        let tg_new = result.trace_generator.as_ref().unwrap();
        let tg_legacy = result_legacy.trace_generator.unwrap();

        // Check if the witness values of the new compiler are the same as the legacy compiler
        let res = tg_new.generate(HashMap::from([("n".to_string(), Fr::from(12))]));
        let res_legacy = tg_legacy.generate(HashMap::from([("n".to_string(), Fr::from(12))]));
        assert_eq!(res.step_instances.len(), res_legacy.step_instances.len());
        for (step, step_legacy) in res.step_instances.iter().zip(res_legacy.step_instances) {
            assert_eq!(step.assignments.len(), step_legacy.assignments.len());
            for assignment in step.assignments.iter() {
                let assignment_legacy = step_legacy
                    .assignments
                    .iter()
                    .find(|x| x.0.annotation() == assignment.0.annotation())
                    .unwrap();
                assert_eq!(assignment.0.annotation(), assignment_legacy.0.annotation());
                assert!(assignment.1.eq(assignment_legacy.1));
            }
        }
    }
}
