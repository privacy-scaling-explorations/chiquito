use std::{collections::HashMap, hash::Hash};

use num_bigint::BigInt;

use crate::{
    compiler::{semantic::SymTable, Message},
    field::Field,
    interpreter::{expr::eval_expr, frame::StackFrame},
    parser::ast::{
        expression::Expression, statement::Statement, tl::TLDecl, DebugSymRef, Identifiable,
        Identifier,
    },
    wit_gen::{StepInstance, SymbolSignalMapping, TraceGenerator, TraceWitness},
};

use self::value::Value;

mod expr;
mod frame;
mod value;

struct Interpreter<'a, F: Field + Hash> {
    mapping: &'a SymbolSignalMapping,
    cur_frame: StackFrame<'a, F>,

    witness: Vec<StepInstance<F>>,
}

impl<'a, F: Field + Hash> Interpreter<'a, F> {
    fn new(symbols: &'a SymTable, mapping: &'a SymbolSignalMapping) -> Self {
        Self {
            mapping,
            cur_frame: StackFrame::new(symbols),
            witness: Vec::default(),
        }
    }

    fn run(
        &mut self,
        ast: &[TLDecl<BigInt, Identifier>],
        input: HashMap<String, F>,
    ) -> Result<TraceWitness<F>, Message> {
        if ast.len() != 1 {
            panic!("More than one machine");
        }

        self.exec_tl(&ast[0], input)?;

        Ok(TraceWitness {
            step_instances: self.witness.clone(),
        })
    }

    fn exec_tl(
        &mut self,
        decl: &TLDecl<BigInt, Identifier>,
        input: HashMap<String, F>,
    ) -> Result<(), Message> {
        match decl {
            TLDecl::MachineDecl {
                dsym,
                id,
                input_params,
                output_params,
                block,
            } => self.exec_machine(dsym, id, input_params, output_params, block, input),
        }
    }

    fn exec_machine(
        &mut self,
        dsym: &DebugSymRef,
        id: &Identifier,
        _input_params: &[Statement<BigInt, Identifier>],
        _output_params: &[Statement<BigInt, Identifier>],
        block: &Statement<BigInt, Identifier>,
        input: HashMap<String, F>,
    ) -> Result<(), Message> {
        let machine_block = get_block_stmts(block);
        let mut next_state: Option<String> = Some("initial".to_string());

        self.cur_frame.enter_machine(id.name());

        for (id, input_value) in input.iter() {
            self.cur_frame.set_value(
                &Identifier::new(id, dsym.clone()),
                &Value::Field(*input_value),
            );
        }

        while next_state.is_some() {
            next_state = self.exec_step(dsym, &machine_block)?;

            self.transition(&next_state);

            if next_state.is_none() && self.cur_frame.get_state().as_str() != "final" {
                panic!(
                    "last state is not final state but {}",
                    self.cur_frame.get_state()
                );
            }
        }

        Ok(())
    }

    fn exec_step(
        &mut self,
        machine_dsym: &DebugSymRef,
        machine_block: &[Statement<BigInt, Identifier>],
    ) -> Result<Option<String>, Message> {
        let state_decl = self.find_state_decl(machine_dsym, machine_block).unwrap();

        if let Statement::StateDecl(_, _, block) = state_decl {
            if let Statement::Block(_, stmts) = *block {
                self.exec_step_block(&stmts)
            } else {
                unreachable!("semantic fail");
            }
        } else {
            unreachable!("semantic fail");
        }
    }

    fn transition(&mut self, next_state: &Option<String>) {
        self.witness
            .push(self.cur_frame.state_transition(self.mapping, next_state));
    }

    fn exec_step_block(
        &mut self,
        stmts: &[Statement<BigInt, Identifier>],
    ) -> Result<Option<String>, Message> {
        let mut next_state: Option<String> = None;

        for stmt in stmts {
            if next_state.is_some() {
                panic!("transition should be the last statement executed")
            }
            next_state = self.exec_step_stmt(stmt)?;
        }

        Ok(next_state)
    }

    fn exec_step_stmt(
        &mut self,
        stmt: &Statement<BigInt, Identifier>,
    ) -> Result<Option<String>, Message> {
        use Statement::*;

        match stmt {
            WGAssignment(_, ids, exprs)
            | SignalAssignment(_, ids, exprs)
            | SignalAssignmentAssert(_, ids, exprs) => {
                for (i, id) in ids.iter().enumerate() {
                    self.exec_assign(id, &exprs[i])?;
                }

                Ok(None)
            }

            IfThen(dsym, cond, block) => {
                let cond = eval_expr(&self.cur_frame, cond.as_ref())?;
                if cond.get_bool().map_err(error_mapper(dsym.clone()))? {
                    if let Statement::Block(_, stmts) = *block.clone() {
                        self.exec_step_block(&stmts)
                    } else {
                        unreachable!("semantic fail");
                    }
                } else {
                    Ok(None)
                }
            }
            IfThenElse(_, cond, block_true, block_false) => {
                let cond = eval_expr(&self.cur_frame, cond.as_ref())?;
                if cond.get_bool().unwrap() {
                    if let Statement::Block(_, stmts) = *block_true.clone() {
                        self.exec_step_block(&stmts)
                    } else {
                        unreachable!("semantic fail");
                    }
                } else if let Statement::Block(_, stmts) = *block_false.clone() {
                    self.exec_step_block(&stmts)
                } else {
                    unreachable!("semantic fail");
                }
            }

            Transition(_, id, block) => {
                if let Statement::Block(_, stmts) = *block.clone() {
                    self.exec_step_block(&stmts)?;
                } else {
                    unreachable!("semantic fail");
                }

                Ok(Some(id.name()))
            }

            SignalDecl(_, _) => Ok(None),
            WGVarDecl(_, _) => Ok(None),
            Block(_, stmts) => self.exec_step_block(stmts),
            Assert(_, _) => Ok(None),
            StateDecl(_, _, _) => Ok(None),
        }
    }

    fn exec_assign(
        &mut self,
        id: &Identifier,
        expr: &Expression<BigInt, Identifier>,
    ) -> Result<(), Message> {
        let value = eval_expr(&self.cur_frame, expr)?;
        // TODO: add context to error message

        self.cur_frame.set_value(id, &value);

        Ok(())
    }

    fn find_state_decl(
        &mut self,
        machine_dsym: &DebugSymRef,
        machine_block: &[Statement<BigInt, Identifier>],
    ) -> Option<Statement<BigInt, Identifier>> {
        for stmt in machine_block {
            if let Statement::StateDecl(_, state_id, _) = stmt {
                if *state_id.name() == self.cur_frame.get_state() {
                    return Some(stmt.clone());
                }
            }
        }

        // final state can be omited
        if self.cur_frame.get_state() == "final" {
            Some(Statement::StateDecl(
                machine_dsym.clone(),
                Identifier::new(self.cur_frame.get_state(), machine_dsym.clone()),
                Box::new(Statement::Block(machine_dsym.clone(), vec![])),
            ))
        } else {
            None
        }
    }
}

/// Runs WG interpreter on a program in AST form.
///
/// * `input` - Map of identifier -> Field value. Where identifier corresponds to the name of an
///   input argument of the machine.
pub fn run<F: Field + Hash>(
    program: &[TLDecl<BigInt, Identifier>],
    symbols: &SymTable,
    mapping: &SymbolSignalMapping,
    input: HashMap<String, F>,
) -> Result<TraceWitness<F>, Message> {
    let mut inter = Interpreter::<F>::new(symbols, mapping);

    inter.run(program, input)
}

/// A trace generator that interprets chiquito source
#[derive(Default, Clone)]
pub struct InterpreterTraceGenerator {
    program: Vec<TLDecl<BigInt, Identifier>>,
    symbols: SymTable,
    mapping: SymbolSignalMapping,
}

impl InterpreterTraceGenerator {
    pub(crate) fn new(
        program: Vec<TLDecl<BigInt, Identifier>>,
        symbols: SymTable,
        mapping: SymbolSignalMapping,
    ) -> Self {
        Self {
            program,
            symbols,
            mapping,
        }
    }

    pub fn evil_assign<F: Field + Hash, S: Into<String>>(
        &self,
        trace: &mut TraceWitness<F>,
        step_num: usize,
        (scope_name, symbol_name): (S, S),
        value: F,
    ) {
        let lhs = self
            .mapping
            .get_queriable(&scope_name.into(), &symbol_name.into(), false);

        trace.step_instances[step_num].assign(lhs, value);
    }
}

impl<F: Field + Hash> TraceGenerator<F> for InterpreterTraceGenerator {
    type TraceArgs = HashMap<String, F>;

    fn generate(&self, args: Self::TraceArgs) -> TraceWitness<F> {
        run(&self.program, &self.symbols, &self.mapping, args).unwrap_or_else(|msgs| {
            panic!("errors when running wg interpreter: {:?}", msgs);
        })
    }
}

fn error_mapper(dsym: DebugSymRef) -> impl Fn(String) -> Message {
    move |msg: String| Message::RuntimeErr {
        msg,
        dsym: dsym.clone(),
    }
}

fn get_block_stmts(stmt: &Statement<BigInt, Identifier>) -> Vec<Statement<BigInt, Identifier>> {
    match stmt {
        Statement::Block(_, stmts) => stmts.clone(),
        _ => panic!("semantic fail"),
    }
}

#[cfg(test)]
mod test {
    use crate::plonkish::backend::halo2::{Halo2Prover, PlonkishHalo2};
    use halo2_proofs::halo2curves::bn256::Fr;
    use rand_chacha::rand_core::block::BlockRng;
    use std::collections::HashMap;

    use crate::{
        compiler::{compile, Config},
        parser::ast::debug_sym_factory::DebugSymRefFactory,
        plonkish::{
            backend::halo2::{halo2_verify, DummyRng},
            compiler::{
                cell_manager::SingleRowCellManager, config,
                step_selector::SimpleStepSelectorBuilder,
            },
        },
        wit_gen::TraceGenerator,
    };

    #[test]
    fn test_run_machine_wg() {
        let code = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
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
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let compiled =
            compile::<Fr>(code, Config::default(), &DebugSymRefFactory::new("", code)).unwrap();

        let result = compiled
            .circuit
            .trace_generator
            .unwrap()
            .generate(HashMap::from([("n".to_string(), Fr::from(12))]));

        println!("{:#?}", result);
    }

    #[test]
    fn test_run_halo2_prover() {
        let code = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
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
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let mut chiquito =
            compile::<Fr>(code, Config::default(), &DebugSymRefFactory::new("", code)).unwrap();

        chiquito.circuit.num_steps = 12;

        let mut plonkish = chiquito.plonkish(config(
            SingleRowCellManager {},
            SimpleStepSelectorBuilder {},
        ));

        let rng = BlockRng::new(DummyRng {});

        let halo2_prover = plonkish.create_halo2_prover(rng);
        assert!(halo2_prover.setup.k == 5);

        let (proof, instance) = halo2_prover.generate_proof(
            plonkish
                .assignment_generator
                .unwrap()
                .generate(HashMap::from([("n".to_string(), Fr::from(12))])),
        );

        let result = halo2_verify(
            proof,
            &halo2_prover.setup.params,
            &halo2_prover.setup.vk,
            instance,
        );
        assert!(result.is_ok());
    }

    #[ignore]
    #[test]
    fn test_run_halo2_mock_prover_evil_witness() {
        let code = "
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
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let mut chiquito =
            compile::<Fr>(code, Config::default(), &DebugSymRefFactory::new("", code)).unwrap();

        chiquito.circuit.num_steps = 12;

        // TODO: re-stablish evil witness
        // chiquito
        // .wit_gen
        // .evil_assign(&mut witness, 1, ("//fibo", "i"), Fr::zero());

        let mut plonkish = chiquito.plonkish(config(
            SingleRowCellManager {},
            SimpleStepSelectorBuilder {},
        ));

        let rng = BlockRng::new(DummyRng {});

        let halo2_prover = plonkish.create_halo2_prover(rng);
        println!("k={}", halo2_prover.setup.k);

        let (proof, instance) = halo2_prover.generate_proof(
            plonkish
                .assignment_generator
                .unwrap()
                .generate(HashMap::from([("n".to_string(), Fr::from(12))])),
        );

        let result = halo2_verify(
            proof,
            &halo2_prover.setup.params,
            &halo2_prover.setup.vk,
            instance,
        );

        println!("result = {:#?}", result);

        if let Err(error) = &result {
            println!("{}", error);
        }
    }
}
