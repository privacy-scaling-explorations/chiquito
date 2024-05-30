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
        program.iter().for_each(|decl| self.analyse_tldcl(decl));
    }

    /// Analyse top level declaration.
    fn analyse_tldcl(&mut self, decl: &TLDecl<BigInt, Identifier>) {
        match decl.clone() {
            TLDecl::MachineDecl {
                dsym,
                id,
                input_params,
                output_params,
                block,
            } => {
                let sym = SymTableEntry {
                    id: id.name(),
                    definition_ref: dsym,
                    usages: vec![],
                    category: SymbolCategory::Machine,
                    ty: None,
                };

                RULES.apply_new_symbol_tldecl(self, decl, &id, &sym);

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
                    id: id.id.name(),
                    definition_ref: dsym.clone(),
                    usages: vec![],
                    category: SymbolCategory::InputSignal,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    id: id.id.name(),
                    definition_ref: dsym.clone(),
                    usages: vec![],
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
                    id: id.id.name(),
                    definition_ref: dsym.clone(),
                    usages: vec![],
                    category: SymbolCategory::OutputSignal,
                    ty: id.ty.clone().map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, param, &id.id, &sym);

                self.symbols
                    .add_output_variable(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.iter().for_each(|id| {
                let sym = SymTableEntry {
                    id: id.id.name(),
                    definition_ref: dsym.clone(),
                    usages: vec![],
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
                        id: id.name(),
                        definition_ref: dsym.clone(),
                        usages: vec![],
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

        if self
            .symbols
            .get_symbol(&self.cur_scope, "final".to_string())
            .is_none()
        {
            let id = Identifier("final".to_string(), 0);
            let stmt = Statement::StateDecl(
                block.get_dsym(),
                id.clone(),
                Box::new(Statement::Block(block.get_dsym(), vec![])),
            );

            let sym = SymTableEntry {
                id: id.name(),
                definition_ref: block.get_dsym(),
                usages: vec![],
                category: SymbolCategory::State,
                ty: None,
            };

            RULES.apply_new_symbol_statement(self, &stmt, &id, &sym);

            self.symbols.add_symbol(&self.cur_scope, id.name(), sym);
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
                    id: id.id.name(),
                    category: SymbolCategory::Signal,
                    usages: vec![],
                    definition_ref: dsym.clone(),
                    ty: id.ty.map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, stmt, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            Statement::WGVarDecl(dsym, ids) => ids.into_iter().for_each(|id| {
                let sym = SymTableEntry {
                    id: id.id.name(),
                    category: SymbolCategory::WGVar,
                    usages: vec![],
                    definition_ref: dsym.clone(),
                    ty: id.ty.map(|ty| ty.name()),
                };

                RULES.apply_new_symbol_statement(self, stmt, &id.id, &sym);

                self.symbols.add_symbol(&self.cur_scope, id.id.name(), sym);
            }),
            // State decl symbols are added in
            // add_state_decls
            Statement::StateDecl(_, _, _) => {}
            Statement::Transition(dsym_ref, id, _) => {
                // Find the corresponding symbol and add usage
                if let Some(entry) = self.symbols.find_symbol(&self.cur_scope, id.name()) {
                    // TODO implement find by id AND category?
                    if entry.symbol.category == SymbolCategory::State {
                        let mut entry = entry.symbol.clone();
                        entry.usages.push(dsym_ref);
                        self.symbols.add_symbol(&self.cur_scope, id.name(), entry);
                    }
                }
            }
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
        self.extract_usages_recursively(&expr);
        RULES.apply_expression(self, &expr)
    }

    fn extract_usages_recursively(&mut self, expr: &Expression<BigInt, Identifier>) {
        match expr.clone() {
            Expression::Query(dsym_ref, id) => {
                // Find the corresponding symbol and add usage
                if let Some(entry) = self.symbols.find_symbol(&self.cur_scope, id.name()) {
                    let mut entry = entry.symbol.clone();
                    entry.usages.push(dsym_ref);
                    self.symbols.add_symbol(&self.cur_scope, id.name(), entry);
                }
            }
            Expression::BinOp {
                dsym: _,
                op: _,
                lhs,
                rhs,
            } => {
                self.extract_usages_recursively(&lhs);
                self.extract_usages_recursively(&rhs);
            }
            Expression::UnaryOp {
                dsym: _,
                op: _,
                sub,
            } => {
                self.extract_usages_recursively(&sub);
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
            r#"AnalysisResult { symbols: "/": ScopeTable { symbols: "\\"fibo\\": SymTableEntry { id: \\"fibo\\", definition_ref: DebugSymRef { start: \\"2:9\\", end: \\"40:13\\" }, usages: [], category: Machine, ty: None }", scope: Global },"//fibo": ScopeTable { symbols: "\\"a\\": SymTableEntry { id: \\"a\\", definition_ref: DebugSymRef { line: 5, cols: \\"13-32\\" }, usages: [], category: Signal, ty: Some(\\"field\\") },\\"b\\": SymTableEntry { id: \\"b\\", definition_ref: DebugSymRef { line: 2, cols: \\"33-48\\" }, usages: [], category: OutputSignal, ty: Some(\\"field\\") },\\"final\\": SymTableEntry { id: \\"final\\", definition_ref: DebugSymRef { start: \\"2:50\\", end: \\"40:13\\" }, usages: [], category: State, ty: None },\\"i\\": SymTableEntry { id: \\"i\\", definition_ref: DebugSymRef { line: 5, cols: \\"13-32\\" }, usages: [], category: Signal, ty: None },\\"initial\\": SymTableEntry { id: \\"initial\\", definition_ref: DebugSymRef { start: \\"10:13\\", end: \\"18:14\\" }, usages: [], category: State, ty: None },\\"middle\\": SymTableEntry { id: \\"middle\\", definition_ref: DebugSymRef { start: \\"20:13\\", end: \\"34:14\\" }, usages: [], category: State, ty: None },\\"n\\": SymTableEntry { id: \\"n\\", definition_ref: DebugSymRef { line: 2, cols: \\"22-30\\" }, usages: [], category: InputSignal, ty: None }", scope: Machine },"//fibo/final": ScopeTable { symbols: "", scope: State },"//fibo/initial": ScopeTable { symbols: "\\"b\\": SymTableEntry { id: \\"b\\", definition_ref: DebugSymRef { line: 2, cols: \\"33-48\\" }, usages: [DebugSymRef { line: 16, cols: \\"30-31\\" }], category: OutputSignal, ty: Some(\\"field\\") },\\"c\\": SymTableEntry { id: \\"c\\", definition_ref: DebugSymRef { line: 11, cols: \\"14-23\\" }, usages: [DebugSymRef { line: 16, cols: \\"33-34\\" }], category: Signal, ty: None },\\"middle\\": SymTableEntry { id: \\"middle\\", definition_ref: DebugSymRef { start: \\"20:13\\", end: \\"34:14\\" }, usages: [DebugSymRef { start: \\"15:14\\", end: \\"17:15\\" }], category: State, ty: None },\\"n\\": SymTableEntry { id: \\"n\\", definition_ref: DebugSymRef { line: 2, cols: \\"22-30\\" }, usages: [DebugSymRef { line: 16, cols: \\"36-37\\" }], category: InputSignal, ty: None }", scope: State },"//fibo/initial/middle": ScopeTable { symbols: "", scope: State },"//fibo/middle": ScopeTable { symbols: "\\"a\\": SymTableEntry { id: \\"a\\", definition_ref: DebugSymRef { line: 5, cols: \\"13-32\\" }, usages: [DebugSymRef { line: 23, cols: \\"20-21\\" }], category: Signal, ty: Some(\\"field\\") },\\"b\\": SymTableEntry { id: \\"b\\", definition_ref: DebugSymRef { line: 2, cols: \\"33-48\\" }, usages: [DebugSymRef { line: 23, cols: \\"24-25\\" }, DebugSymRef { line: 31, cols: \\"42-43\\" }], category: OutputSignal, ty: Some(\\"field\\") },\\"c\\": SymTableEntry { id: \\"c\\", definition_ref: DebugSymRef { line: 21, cols: \\"14-23\\" }, usages: [DebugSymRef { line: 27, cols: \\"38-39\\" }, DebugSymRef { line: 31, cols: \\"45-46\\" }], category: Signal, ty: None },\\"final\\": SymTableEntry { id: \\"final\\", definition_ref: DebugSymRef { start: \\"2:50\\", end: \\"40:13\\" }, usages: [DebugSymRef { start: \\"26:15\\", end: \\"28:16\\" }], category: State, ty: None },\\"i\\": SymTableEntry { id: \\"i\\", definition_ref: DebugSymRef { line: 5, cols: \\"13-32\\" }, usages: [DebugSymRef { line: 25, cols: \\"17-18\\" }, DebugSymRef { line: 27, cols: \\"31-32\\" }, DebugSymRef { line: 31, cols: \\"35-36\\" }], category: Signal, ty: None },\\"middle\\": SymTableEntry { id: \\"middle\\", definition_ref: DebugSymRef { start: \\"20:13\\", end: \\"34:14\\" }, usages: [DebugSymRef { start: \\"30:15\\", end: \\"32:16\\" }], category: State, ty: None },\\"n\\": SymTableEntry { id: \\"n\\", definition_ref: DebugSymRef { line: 2, cols: \\"22-30\\" }, usages: [DebugSymRef { line: 25, cols: \\"26-27\\" }, DebugSymRef { line: 27, cols: \\"41-42\\" }, DebugSymRef { line: 31, cols: \\"48-49\\" }], category: InputSignal, ty: None }", scope: State },"//fibo/middle/final": ScopeTable { symbols: "", scope: State },"//fibo/middle/middle": ScopeTable { symbols: "", scope: State }, messages: [] }"#
        )
    }
}
