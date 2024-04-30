use std::collections::HashMap;

use num_bigint::BigInt;

use crate::{
    parser::ast::{statement::Statement, tl::TLDecl, DebugSymRef, Identifiable, Identifier},
    poly::Expr,
};

use super::{abepi::CompilationUnit, semantic::SymTable};

pub(super) fn interpret(
    ast: &[TLDecl<BigInt, Identifier>],
    _symbols: &SymTable,
) -> Setup<BigInt, Identifier> {
    let mut interpreter = SetupInterpreter {
        abepi: CompilationUnit::default(),
        setup: Setup::default(),
        current_machine: String::default(),
        current_state: String::default(),
    };

    interpreter.interpret(ast);

    interpreter.setup
}

pub(super) type Setup<F, V> = HashMap<String, HashMap<String, Vec<Expr<F, V, ()>>>>;

pub(super) struct SetupInterpreter {
    abepi: CompilationUnit<BigInt, Identifier, ()>,

    setup: Setup<BigInt, Identifier>,

    current_machine: String,
    current_state: String,
}

impl SetupInterpreter {
    pub(super) fn interpret(&mut self, ast: &[TLDecl<BigInt, Identifier>]) {
        use TLDecl::*;
        ast.iter().for_each(|tl| match tl {
            MachineDecl {
                dsym,
                id,
                input_params,
                output_params,
                block,
            } => self.interpret_machine(dsym, id, input_params, output_params, block),
        });
    }

    fn interpret_machine(
        &mut self,
        _dsym: &DebugSymRef,
        id: &Identifier,
        _input_params: &[Statement<BigInt, Identifier>],
        _output_params: &[Statement<BigInt, Identifier>],
        block: &Statement<BigInt, Identifier>,
    ) {
        self.current_machine = id.name();
        self.setup.insert(id.name(), HashMap::default());
        self.interpret_machine_statement(block);
    }

    fn interpret_machine_statement(&mut self, stmt: &Statement<BigInt, Identifier>) {
        match stmt {
            Statement::Block(_, block) => {
                block
                    .iter()
                    .for_each(|stmt| self.interpret_machine_statement(stmt));
            }
            Statement::StateDecl(dsym, id, stmt) => self.interpret_state_decl(dsym, id, stmt),
            Statement::SignalDecl(_, _) => {}
            Statement::WGVarDecl(_, _) => {}

            _ => unreachable!("semantic analyser should prevent this"),
        }
    }

    fn interpret_state_decl(
        &mut self,
        _dsym: &DebugSymRef,
        id: &Identifier,
        stmt: &Statement<BigInt, Identifier>,
    ) {
        self.current_state = id.name();
        self.setup
            .get_mut(&self.current_machine)
            .unwrap()
            .insert(id.name(), Vec::default());
        self.interpret_state_statement(stmt);
    }

    fn interpret_state_statement(&mut self, stmt: &Statement<BigInt, Identifier>) {
        use Statement::*;
        let result = match stmt {
            Block(_, block) => {
                block
                    .iter()
                    .for_each(|stmt| self.interpret_state_statement(stmt));
                vec![]
            }
            Assert(_, _)
            | SignalAssignmentAssert(_, _, _)
            | IfThen(_, _, _)
            | IfThenElse(_, _, _, _)
            | Transition(_, _, _) => self.abepi.compile_statement(stmt.clone()),

            StateDecl(_, _, _) => unreachable!("semantic analyser should prevent this"),

            SignalAssignment(_, _, _) | WGAssignment(_, _, _) => vec![],
            SignalDecl(_, _) | WGVarDecl(_, _) => vec![],
        };

        self.add_pis(result.into_iter().map(|cr| cr.anti_booly).collect());
    }

    fn add_pis(&mut self, pis: Vec<Expr<BigInt, Identifier, ()>>) {
        self.setup
            .get_mut(&self.current_machine)
            .unwrap()
            .get_mut(&self.current_state)
            .unwrap()
            .extend(pis);
    }
}
