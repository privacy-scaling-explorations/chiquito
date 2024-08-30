use itertools::Itertools;
use num_bigint::BigInt;

use crate::{
    compiler::{
        semantic::{
            rules::RULES, AnalysisResult, ScopeTable, SymTable, SymTableEntry, SymbolCategory,
        },
        Message,
    },
    parser::ast::{
        expression::Expression, statement::Statement, tl::TLDecl, DebugSymRef, Identifiable,
        Identifier,
    },
};

/// Public interface to semantic analyser.
/// Returns symbol table and messages.
pub fn analyse(program: &[TLDecl<BigInt, Identifier>]) -> AnalysisResult {
    let mut analyser = Analyser::default();

    analyser.analyse(program);

    AnalysisResult::from(analyser)
}

/// Semantic analyser.
pub(super) struct Analyser {
    pub(super) symbols: SymTable,
    pub(super) messages: Vec<Message>,
    pub(super) cur_scope: Vec<String>,
}

impl Default for Analyser {
    fn default() -> Self {
        let mut symbols = SymTable::default();
        symbols
            .scopes
            .insert("/".to_string(), ScopeTable::default());

        Self {
            symbols,
            messages: Vec::default(),
            cur_scope: vec!["/".to_string()],
        }
    }
}

impl Analyser {
    /// Analyse chiquito AST.
    fn analyse(&mut self, program: &[TLDecl<BigInt, Identifier>]) {
        program
            .iter()
            .for_each(|decl: &TLDecl<BigInt, Identifier>| self.collect_tl_decl(decl));
        program.iter().for_each(|decl| self.analyse_tldcl(decl));
    }

    /// Collect a top level declaration to later perform necessary checks (e.g., validate the
    /// calls of machines from other machines).
    fn collect_tl_decl(&mut self, decl: &TLDecl<BigInt, Identifier>) {
        match decl.clone() {
            TLDecl::MachineDecl {
                dsym: _,
                id,
                input_params,
                output_params,
                block: _,
            } => {
                let sym = SymTableEntry::new_machine(
                    id.name(),
                    id.debug_sym_ref(),
                    SymbolCategory::Machine,
                    None,
                    input_params
                        .iter()
                        .map(|param| match param {
                            Statement::SignalDecl(_, decls) | Statement::WGVarDecl(_, decls) => {
                                if decls.len() != 1 {
                                    unreachable!("Each input should be a single identifier");
                                }
                                decls[0].id.name()
                            }
                            _ => unreachable!("Inputs should be signals or vars"),
                        })
                        .collect_vec(),
                    output_params
                        .iter()
                        .map(|param| match param {
                            Statement::SignalDecl(_, decls) | Statement::WGVarDecl(_, decls) => {
                                if decls.len() != 1 {
                                    unreachable!("Each output should be a single identifier");
                                }
                                decls[0].id.name()
                            }
                            _ => unreachable!("Outputs should be signals or vars"),
                        })
                        .collect_vec(),
                );

                RULES.apply_new_symbol_tldecl(self, decl, &id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.name(), sym);

                self.enter_new_scope(id.name());

                self.analyse_machine_input_params(input_params);

                self.analyse_machine_output_params(output_params);

                self.exit_scope();
            }
        }
    }

    /// Analyse top level declaration.
    fn analyse_tldcl(&mut self, decl: &TLDecl<BigInt, Identifier>) {
        match decl.clone() {
            TLDecl::MachineDecl {
                dsym: _,
                id,
                input_params: _,
                output_params: _,
                block,
            } => {
                self.analyse_machine(id, block);
            }
        }
    }

    fn analyse_machine(&mut self, id: Identifier, block: Statement<BigInt, Identifier>) {
        self.enter_new_scope(id.name());

        self.add_state_decls(&block);

        self.analyse_statement(block);

        self.exit_scope();
    }

    fn analyse_machine_input_params(&mut self, params: Vec<Statement<BigInt, Identifier>>) {
        params.iter().for_each(|param| match param {
            Statement::SignalDecl(_, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::InputSignal,
                    id.ty.clone().map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(_, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::InputWGVar,
                    id.ty.clone().map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            _ => unreachable!("parser should only produce signals and vars"),
        });
    }

    fn analyse_machine_output_params(&mut self, params: Vec<Statement<BigInt, Identifier>>) {
        params.iter().for_each(|param| match param {
            Statement::SignalDecl(_, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::OutputSignal,
                    id.ty.clone().map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols
                    .add_output_variable(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(_, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::OutputWGVar,
                    id.ty.clone().map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols
                    .add_output_variable(&self.cur_scope, id.id.name(), sym);
            }),
            _ => unreachable!("parser should only produce signals and vars"),
        });
    }

    /// Add state declarations of a machine.
    /// This is done before analysing the rest of the machine because you can refer to a state in a
    /// transition before it is declared. This does not happen with other symbols that need to be
    /// declared before using.
    fn add_state_decls(&mut self, block: &Statement<BigInt, Identifier>) {
        if let Statement::Block(_, stmts) = block {
            stmts.iter().for_each(|stmt| {
                if let Statement::StateDecl(_, id, _) = stmt {
                    let sym = SymTableEntry::new(
                        id.name(),
                        id.debug_sym_ref(),
                        SymbolCategory::State,
                        None,
                    );

                    RULES.apply_new_symbol_statement(self, stmt, id, &sym);

                    self.symbols.add_symbol(&self.cur_scope, id.name(), sym);
                }
            })
        } else {
            unreachable!("the parser should produce machine declaration with a block");
        }
    }

    fn analyse_state(&mut self, id: Identifier, block: Statement<BigInt, Identifier>) {
        self.enter_new_scope(id.name());

        self.analyse_statement(block);

        self.exit_scope();
    }

    fn analyse_statement(&mut self, stmt: Statement<BigInt, Identifier>) {
        self.statement_add_symbols(&stmt);
        self.analyse_statement_recursive(stmt);
    }

    fn statement_add_symbols(&mut self, stmt: &Statement<BigInt, Identifier>) {
        match stmt.clone() {
            Statement::SignalDecl(_, ids) => ids.into_iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::Signal,
                    id.ty.map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, stmt, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(_, ids) => ids.into_iter().for_each(|id| {
                let sym = SymTableEntry::new(
                    id.id.name(),
                    id.id.debug_sym_ref(),
                    SymbolCategory::WGVar,
                    id.ty.map(|ty| ty.name()),
                );

                RULES.apply_new_symbol_statement(self, stmt, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            // State decl symbols are added in
            // add_state_decls
            Statement::StateDecl(_, _, _) => {}
            _ => {}
        }
    }

    fn analyse_statement_recursive(&mut self, stmt: Statement<BigInt, Identifier>) {
        RULES.apply_statement(self, &stmt);

        match stmt {
            Statement::Assert(_, expr) => self.analyse_expression(expr),
            Statement::SignalAssignment(_, ids, exprs) => {
                exprs
                    .into_iter()
                    .for_each(|expr| self.analyse_expression(expr));
                self.collect_id_usages(&ids);
            }
            Statement::SignalAssignmentAssert(_, ids, exprs) => {
                exprs
                    .into_iter()
                    .for_each(|expr| self.analyse_expression(expr));
                self.collect_id_usages(&ids);
            }
            Statement::WGAssignment(_, _, exprs) => exprs
                .into_iter()
                .for_each(|expr| self.analyse_expression(expr)),
            Statement::IfThen(_, cond, when_true) => {
                self.analyse_expression(*cond);
                self.analyse_statement(*when_true);
            }
            Statement::IfThenElse(_, cond, when_true, when_false) => {
                self.analyse_expression(*cond);
                self.analyse_statement(*when_true);
                self.analyse_statement(*when_false);
            }

            Statement::StateDecl(_, id, block) => self.analyse_state(id, *block),
            Statement::Transition(_, id, block) => {
                self.analyse_statement(*block);
                self.collect_id_usages(&[id]);
            }

            Statement::Block(_, stmts) => stmts
                .into_iter()
                .for_each(|stmt| self.analyse_statement(stmt)),

            Statement::SignalDecl(_, _) => {}
            Statement::WGVarDecl(_, _) => {}
            Statement::HyperTransition(_, ref assign_call, ref state_transition) => {
                self.analyse_statement_recursive(*assign_call.clone());
                self.analyse_statement_recursive(*state_transition.clone());
            }
        }
    }

    fn analyse_expression(&mut self, expr: Expression<BigInt, Identifier>) {
        RULES.apply_expression(self, &expr);
        self.extract_usages_expression(&expr);
    }

    fn collect_id_usages(&mut self, ids: &[Identifier]) {
        for id in ids {
            self.symbols
                .add_symbol_usage(&self.cur_scope, id.name(), id.debug_sym_ref());
        }
    }

    fn extract_usages_expression(&mut self, expr: &Expression<BigInt, Identifier>) {
        match expr.clone() {
            Expression::Query(_, id) => {
                self.collect_id_usages(&[id]);
            }
            Expression::BinOp {
                dsym: _,
                op: _,
                lhs,
                rhs,
            } => {
                self.extract_usages_expression(&lhs);
                self.extract_usages_expression(&rhs);
            }
            Expression::UnaryOp {
                dsym: _,
                op: _,
                sub,
            } => {
                self.extract_usages_expression(&sub);
            }
            Expression::Call(_, fun, exprs) => {
                self.collect_id_usages(&[fun]);
                exprs
                    .into_iter()
                    .for_each(|expr| self.extract_usages_expression(&expr));
            }
            _ => {}
        }
    }

    pub(super) fn error<S: Into<String>>(&mut self, msg: S, dsym: &DebugSymRef) {
        self.messages.push(Message::SemErr {
            msg: msg.into(),
            dsym: dsym.clone(),
        })
    }

    fn enter_new_scope(&mut self, id: String) {
        self.cur_scope.push(id)
    }

    fn exit_scope(&mut self) {
        self.cur_scope.pop();
    }
}

#[cfg(test)]
mod test {
    use crate::parser::{ast::debug_sym_factory::DebugSymRefFactory, lang};

    use super::analyse;

    #[test]
    fn test_analyser_machine() {
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

        let debug_sym_factory = DebugSymRefFactory::new("", circuit);
        let decls = lang::TLDeclsParser::new()
            .parse(&debug_sym_factory, circuit)
            .unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result),
            r#"AnalysisResult { symbols: /: ScopeTable { symbols: "fibo: SymTableEntry { id: \"fibo\", definition_ref: nofile:2:17, usages: [], category: Machine, ty: None, ins: Some([\"n\"]), outs: Some([\"b\"]) }", scope: Global },//fibo: ScopeTable { symbols: "a: SymTableEntry { id: \"a\", definition_ref: nofile:5:20, usages: [nofile:13:17, nofile:16:15, nofile:23:20, nofile:31:20], category: Signal, ty: Some(\"field\"), ins: None, outs: None },b: SymTableEntry { id: \"b\", definition_ref: nofile:2:40, usages: [nofile:13:20, nofile:16:30, nofile:16:19, nofile:23:24, nofile:27:20, nofile:31:42, nofile:31:24], category: OutputSignal, ty: Some(\"field\"), ins: None, outs: None },i: SymTableEntry { id: \"i\", definition_ref: nofile:5:30, usages: [nofile:13:14, nofile:25:17, nofile:27:31, nofile:27:16, nofile:31:35, nofile:31:16], category: Signal, ty: None, ins: None, outs: None },initial: SymTableEntry { id: \"initial\", definition_ref: nofile:10:19, usages: [], category: State, ty: None, ins: None, outs: None },middle: SymTableEntry { id: \"middle\", definition_ref: nofile:20:19, usages: [nofile:15:17, nofile:30:18], category: State, ty: None, ins: None, outs: None },n: SymTableEntry { id: \"n\", definition_ref: nofile:2:29, usages: [nofile:16:36, nofile:16:23, nofile:25:26, nofile:27:41, nofile:27:24, nofile:31:48, nofile:31:28], category: InputSignal, ty: None, ins: None, outs: None }", scope: Machine },//fibo/initial: ScopeTable { symbols: "c: SymTableEntry { id: \"c\", definition_ref: nofile:11:21, usages: [nofile:13:23, nofile:16:33], category: Signal, ty: None, ins: None, outs: None }", scope: State },//fibo/middle: ScopeTable { symbols: "c: SymTableEntry { id: \"c\", definition_ref: nofile:21:21, usages: [nofile:23:14, nofile:27:38, nofile:31:45], category: Signal, ty: None, ins: None, outs: None }", scope: State }, messages: [] }"#
        );
    }
}
