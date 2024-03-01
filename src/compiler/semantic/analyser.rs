use num_bigint::BigInt;

use crate::{
    compiler::semantic::{
        rules::RULES, AnalysisResult, Message, ScopeTable, SymTable, SymTableEntry, SymbolCategory,
    },
    parser::ast::{
        expression::Expression, statement::Statement, tl::TLDecl, DebugSymRef, Identifiable,
        Identifier,
    },
};

/// Public interface to semantic analyser.
/// Returns symbol table and messages.
pub fn analyse(program: Vec<TLDecl<BigInt, Identifier>>) -> AnalysisResult {
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
    fn analyse(&mut self, program: Vec<TLDecl<BigInt, Identifier>>) {
        program
            .into_iter()
            .for_each(|decl| self.analyse_tldcl(decl));
    }

    /// Analyse top level declaration.
    fn analyse_tldcl(&mut self, decl: TLDecl<BigInt, Identifier>) {
        match decl.clone() {
            TLDecl::MachineDecl {
                dsym,
                id,
                input_params,
                output_params,
                block,
            } => {
                let sym = SymTableEntry {
                    definition_ref: dsym,
                    category: SymbolCategory::Machine,
                    ty: None,
                };

                RULES.apply_new_symbol_tldecl(self, &decl, &id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.name(), sym);

                self.analyse_machine(id, input_params, output_params, block);
            }
        }
    }

    fn analyse_machine(
        &mut self,
        id: Identifier,
        input_params: Vec<Statement<BigInt, Identifier>>,
        output_params: Vec<Statement<BigInt, Identifier>>,
        block: Statement<BigInt, Identifier>,
    ) {
        self.enter_new_scope(id.name());

        self.analyse_machine_input_params(input_params);
        self.analyse_machine_output_params(output_params);

        self.add_state_decls(&block);

        self.analyse_statement(block);

        self.exit_scope();
    }

    fn analyse_machine_input_params(&mut self, params: Vec<Statement<BigInt, Identifier>>) {
        params.iter().for_each(|param| match param {
            Statement::SignalDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    definition_ref: dsym.clone(),
                    category: SymbolCategory::InputSignal,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    definition_ref: dsym.clone(),
                    category: SymbolCategory::InputWGVar,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            _ => unreachable!("parser should only produce signals and vars"),
        });
    }

    fn analyse_machine_output_params(&mut self, params: Vec<Statement<BigInt, Identifier>>) {
        params.iter().for_each(|param| match param {
            Statement::SignalDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    definition_ref: dsym.clone(),
                    category: SymbolCategory::OutputSignal,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols
                    .add_output_variable(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    definition_ref: dsym.clone(),
                    category: SymbolCategory::OutputWGVar,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

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
                if let Statement::StateDecl(dsym, id, _) = stmt {
                    let sym = SymTableEntry {
                        definition_ref: dsym.clone(),
                        category: SymbolCategory::State,
                        ty: None,
                    };

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

        RULES.apply_statement(self, &stmt);

        self.analyse_statement_recursive(stmt);
    }

    fn statement_add_symbols(&mut self, stmt: &Statement<BigInt, Identifier>) {
        match stmt.clone() {
            Statement::SignalDecl(dsym, ids) => ids.into_iter().for_each(|id| {
                let sym = SymTableEntry {
                    category: SymbolCategory::Signal,
                    definition_ref: dsym.clone(),
                    ty: id.ty.map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, stmt, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.into_iter().for_each(|id| {
                let sym = SymTableEntry {
                    category: SymbolCategory::WGVar,
                    definition_ref: dsym.clone(),
                    ty: id.ty.map(|ty| ty.name()),
                };

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
        match stmt {
            Statement::Assert(_, expr) => self.analyse_expression(expr),
            Statement::SignalAssignment(_, _, exprs) => exprs
                .into_iter()
                .for_each(|expr| self.analyse_expression(expr)),
            Statement::SignalAssignmentAssert(_, _, exprs) => exprs
                .into_iter()
                .for_each(|expr| self.analyse_expression(expr)),
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
            Statement::Transition(_, _, block) => self.analyse_statement(*block),

            Statement::Block(_, stmts) => stmts
                .into_iter()
                .for_each(|stmt| self.analyse_statement(stmt)),

            Statement::SignalDecl(_, _) => {}
            Statement::WGVarDecl(_, _) => {}
        }
    }

    fn analyse_expression(&mut self, expr: Expression<BigInt, Identifier>) {
        RULES.apply_expression(self, &expr)
    }

    pub(super) fn error<S: Into<String>>(&mut self, msg: S, dsym: &DebugSymRef) {
        self.messages.push(Message::Err {
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
    use crate::parser::lang;

    use super::analyse;

    #[test]
    fn test_analyser_machine() {
        let circuit = "
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
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(decls);

        assert_eq!(
            format!("{:?}", result),
            r#"AnalysisResult { symbols: "/": ScopeTable { symbols: "\"fibo\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: Machine, ty: None }", scope: Global },"//fibo": ScopeTable { symbols: "\"a\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: Signal, ty: Some(\"field\") },\"b\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: OutputSignal, ty: Some(\"field\") },\"i\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: Signal, ty: None },\"initial\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: State, ty: None },\"middle\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: State, ty: None },\"n\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: InputSignal, ty: None }", scope: Machine },"//fibo/initial": ScopeTable { symbols: "\"c\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: Signal, ty: None }", scope: State },"//fibo/middle": ScopeTable { symbols: "\"c\": SymTableEntry { definition_ref: DebugSymRef { start: 0, end: 0 }, category: Signal, ty: None }", scope: State }, messages: [] }"#
        )
    }
}
