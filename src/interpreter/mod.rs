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
    wit_gen::{StepInstance, SymbolSignalMapping},
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
    pub fn new(symbols: &'a SymTable, mapping: &'a SymbolSignalMapping) -> Self {
        Self {
            mapping,
            cur_frame: StackFrame::new(symbols),
            witness: Vec::default(),
        }
    }

    pub fn run(
        &mut self,
        ast: &[TLDecl<BigInt, Identifier>],
        input: HashMap<String, F>,
    ) -> Result<Vec<StepInstance<F>>, Message> {
        if ast.len() != 1 {
            panic!("More than one machine");
        }

        self.exec_tl(&ast[0], input)?;

        Ok(self.witness.clone())
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
        _dsym: &DebugSymRef,
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
            self.cur_frame.set_value(id, &Value::Field(*input_value));
        }

        while next_state.is_some() {
            next_state = self.exec_step(&machine_block)?;

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
        machine_block: &[Statement<BigInt, Identifier>],
    ) -> Result<Option<String>, Message> {
        let state_decl = self.find_state_decl(machine_block).unwrap();

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
                DebugSymRef::new(0, 0),
                self.cur_frame.get_state().into(),
                Box::new(Statement::Block(DebugSymRef::new(0, 0), vec![])),
            ))
        } else {
            None
        }
    }
}

pub fn run<F: Field + Hash>(
    ast: &[TLDecl<BigInt, Identifier>],
    symbols: &SymTable,
    mapping: &SymbolSignalMapping,
    input: HashMap<String, F>,
) -> Result<Vec<StepInstance<F>>, Message> {
    let mut inter = Interpreter::<F>::new(symbols, mapping);

    inter.run(ast, input)
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
    use std::collections::HashMap;

    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    use crate::{
        compiler::{compile, Config},
        plonkish::{
            backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit},
            compiler::{
                cell_manager::SingleRowCellManager, config,
                step_selector::SimpleStepSelectorBuilder,
            },
        },
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

        let compiled = compile::<Fr>(code, Config::default()).unwrap();

        let result = compiled
            .wit_gen
            .generate(HashMap::from([("n".to_string(), Fr::from(12))]));

        println!("{:#?}", result);
    }

    #[test]
    fn test_run_halo2_mock_prover() {
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

        let mut chiquito = compile::<Fr>(code, Config::default()).unwrap();

        chiquito.circuit.num_steps = 12;

        let witness = chiquito
            .wit_gen
            .generate(HashMap::from([("n".to_string(), Fr::from(12))]))
            .unwrap();

        let plonkish = chiquito.plonkish(config(
            SingleRowCellManager {},
            SimpleStepSelectorBuilder {},
        ));

        let compiled = chiquito2Halo2(plonkish.0);

        let circuit = ChiquitoHalo2Circuit::new(
            compiled,
            plonkish.1.map(|g| g.generate_with_witness(witness)),
        );

        let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

        let result = prover.verify();

        assert!(result.is_ok());
    }

    #[test]
    fn test_run_halo2_mock_prover_evil_witness() {
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

        let mut chiquito = compile::<Fr>(code, Config::default()).unwrap();

        chiquito.circuit.num_steps = 12;

        let mut witness = chiquito
            .wit_gen
            .generate(HashMap::from([("n".to_string(), Fr::from(12))]))
            .unwrap();

        chiquito
            .wit_gen
            .evil_assign(&mut witness, 1, ("//fibo", "i"), Fr::zero());

        let plonkish = chiquito.plonkish(config(
            SingleRowCellManager {},
            SimpleStepSelectorBuilder {},
        ));

        let compiled = chiquito2Halo2(plonkish.0);

        let circuit = ChiquitoHalo2Circuit::new(
            compiled,
            plonkish.1.map(|g| g.generate_with_witness(witness)),
        );

        let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

        let result = prover.verify();

        assert!(result.is_err());

        if let Err(result) = result {
            println!("{}", result.len());
        }
    }
}
