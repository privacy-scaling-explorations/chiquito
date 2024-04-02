use std::{
    collections::HashMap,
    fmt::{Debug, Display},
};

use num_bigint::BigInt;

use itertools::Itertools;

use crate::{
    compiler::semantic::analyser::Analyser,
    parser::ast::{
        expression::Expression, statement::Statement, tl::TLDecl, DebugSymRef, Identifier,
    },
};

/// Category of a symbol
#[derive(Clone, PartialEq, Debug)]
enum SymbolCategory {
    Machine,
    State,

    Signal,
    WGVar,

    InputSignal,
    OutputSignal,
    InoutSignal,

    InputWGVar,
    OutputWGVar,
    InoutWGVar,
}

/// Category of a scope
#[derive(Clone, Debug)]
pub enum ScopeCategory {
    Global,
    Machine,
    State,
}

/// Information about a symbol
#[derive(Clone, Debug)]
pub struct SymTableEntry {
    definition_ref: DebugSymRef,
    category: SymbolCategory,
    /// Type
    ty: Option<String>,
}

impl SymTableEntry {
    fn is_scoped(&self) -> bool {
        matches!(
            self.category,
            SymbolCategory::Machine | SymbolCategory::State
        )
    }

    fn get_type(&self) -> &str {
        match &self.ty {
            Some(ty) => ty,
            None => "field",
        }
    }
}

/// Extra information when symbol is found in a scope or a containing scope
pub struct FoundSymbol {
    symbol: SymTableEntry,
    scope: ScopeCategory,
    level: usize,
}

/// Contains the symbols of an scope
#[derive(Clone)]
pub struct ScopeTable {
    symbols: HashMap<String, SymTableEntry>,
    scope: ScopeCategory,
}

impl Default for ScopeTable {
    fn default() -> Self {
        Self {
            symbols: HashMap::default(),
            scope: ScopeCategory::Global,
        }
    }
}

impl Debug for ScopeTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbols = self
            .symbols
            .keys()
            .sorted()
            .map(|id| format!("\"{}\": {:?}", id, self.symbols[id]))
            .collect::<Vec<_>>()
            .join(",");

        f.debug_struct("ScopeTable")
            .field("symbols", &symbols)
            .field("scope", &self.scope)
            .finish()
    }
}

impl From<SymTableEntry> for ScopeTable {
    fn from(entry: SymTableEntry) -> Self {
        ScopeTable {
            symbols: HashMap::default(),
            scope: match entry.category {
                SymbolCategory::Machine => ScopeCategory::Machine,
                SymbolCategory::State => ScopeCategory::State,
                _ => unreachable!(), // Other symbols don't have their own symbol table
            },
        }
    }
}

impl ScopeTable {
    fn get_symbol(&self, id: String) -> Option<&SymTableEntry> {
        self.symbols.get(&id)
    }

    fn add_symbol(&mut self, id: String, entry: SymTableEntry) {
        self.symbols.insert(id, entry);
    }
}

/// Symbol table for a chiquito program
#[derive(Default)]
pub struct SymTable {
    scopes: HashMap<String, ScopeTable>,
}

impl Display for SymTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .scopes
            .iter()
            .fold("".to_string(), |acc, (scope, table)| {
                format!("{}{}\n  {:?}\n", acc, scope, table)
            });

        write!(f, "{}", result)
    }
}

impl Debug for SymTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .scopes
            .keys()
            .sorted()
            .map(|scope| format!("\"{}\": {:?}", scope, self.scopes[scope]))
            .collect::<Vec<_>>()
            .join(",");

        write!(f, "{}", result)
    }
}

impl SymTable {
    /// Get a symbol in a particular scope.
    /// scope parameter is an array of the scope names on the path.
    pub fn get_symbol(&self, scope: &[String], id: String) -> Option<&SymTableEntry> {
        self.scopes
            .get(&Self::get_key(scope))
            .expect("scope not found")
            .get_symbol(id)
    }

    /// Finds a symbol in a scope or any of the containing scopes.
    pub fn find_symbol(&self, scope: &[String], id: String) -> Option<FoundSymbol> {
        let mut level = 0;
        while level < scope.len() {
            let table = self
                .scopes
                .get(&Self::get_key_level(scope, level))
                .expect("scope not found");
            let symbol = table.get_symbol(id.clone());

            if symbol.is_some() {
                return symbol.map(|symbol| FoundSymbol {
                    symbol: symbol.clone(),
                    scope: table.scope.clone(),
                    level,
                });
            }

            level += 1;
        }

        None
    }

    /// Add a symbol
    pub fn add_symbol(&mut self, scope: &[String], id: String, entry: SymTableEntry) {
        let scope_key = Self::get_key(scope);
        self.scopes
            .get_mut(&scope_key)
            .unwrap_or_else(|| panic!("scope {} not found", &scope_key))
            .add_symbol(id.clone(), entry.clone());

        if entry.is_scoped() {
            self.scopes
                .insert(format!("{}/{}", &scope_key, id), ScopeTable::from(entry));
        }
    }

    /// Add an output variable symbol.
    /// This is special because if there is an input variable symbol with the same identifier, it
    /// should create a Input/Output symbol.
    pub fn add_output_variable(&mut self, scope: &[String], id: String, mut entry: SymTableEntry) {
        let prev_symbol = self.get_symbol(scope, id.clone());
        if let Some(prev_symbol) = prev_symbol {
            match prev_symbol.category {
                SymbolCategory::InputSignal => {
                    assert_eq!(entry.category, SymbolCategory::OutputSignal); // TODO; convert this to a sematic error

                    entry.category = SymbolCategory::InoutSignal;
                }
                SymbolCategory::InputWGVar => {
                    assert_eq!(entry.category, SymbolCategory::OutputWGVar); // TODO; convert this to a sematic error

                    entry.category = SymbolCategory::InoutWGVar;
                }

                _ => unreachable!(
                    "should not be output with same name as an identifier that is not input"
                ), // TODO; convert this to a sematic error
            }
        }

        self.add_symbol(scope, id, entry);
    }

    fn get_key(scope: &[String]) -> String {
        scope.join("/")
    }

    fn get_key_level(scope: &[String], level: usize) -> String {
        if level == 0 {
            Self::get_key(scope)
        } else {
            scope
                .iter()
                .rev()
                .skip(level)
                .rev()
                .cloned()
                .collect::<Vec<_>>()
                .join("/")
        }
    }
}

/// Semantic Analyser message.
#[derive(Debug)]
pub enum Message {
    Err { msg: String, dsym: DebugSymRef },
}

/// Result from running the semantic analyser.
#[derive(Debug)]
pub struct AnalysisResult {
    pub symbols: SymTable,
    pub messages: Vec<Message>,
}

impl From<Analyser> for AnalysisResult {
    fn from(analyser: Analyser) -> Self {
        AnalysisResult {
            symbols: analyser.symbols,
            messages: analyser.messages,
        }
    }
}

// Rule types.
// Rules are implemented as functions of this types.

type ExpressionRule = fn(analyser: &mut Analyser, expr: &Expression<BigInt, Identifier>);
type StatementRule = fn(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>);
type NewSymbolRule = fn(
    analyser: &mut Analyser,
    expr: &Statement<BigInt, Identifier>,
    id: &Identifier,
    symbol: &SymTableEntry,
);
type NewTLSymbolRule = fn(
    analyser: &mut Analyser,
    decl: &TLDecl<BigInt, Identifier>,
    id: &Identifier,
    symbol: &SymTableEntry,
);

/// Set of rules used by the semantic analyser.
struct RuleSet {
    expression: Vec<ExpressionRule>,
    statement: Vec<StatementRule>,
    new_symbol: Vec<NewSymbolRule>,
    new_tl_symbol: Vec<NewTLSymbolRule>,
}

impl RuleSet {
    /// Apply expression rules.
    pub(self) fn apply_expression(
        &self,
        analyser: &mut Analyser,
        expr: &Expression<BigInt, Identifier>,
    ) {
        self.expression.iter().for_each(|rule| rule(analyser, expr));
    }

    /// Apply statement rules.
    pub(self) fn apply_statement(
        &self,
        analyser: &mut Analyser,
        stmt: &Statement<BigInt, Identifier>,
    ) {
        self.statement.iter().for_each(|rule| rule(analyser, stmt));
    }

    /// Apply new symbol top level declaration rules.
    pub(self) fn apply_new_symbol_tldecl(
        &self,
        analyser: &mut Analyser,
        tldecl: &TLDecl<BigInt, Identifier>,
        id: &Identifier,
        symbol: &SymTableEntry,
    ) {
        self.new_tl_symbol
            .iter()
            .for_each(|rule| rule(analyser, tldecl, id, symbol));
    }

    /// Apply new symbol (not top level) rules.
    pub(self) fn apply_new_symbol_statement(
        &self,
        analyser: &mut Analyser,
        stmt: &Statement<BigInt, Identifier>,
        id: &Identifier,
        symbol: &SymTableEntry,
    ) {
        self.new_symbol
            .iter()
            .for_each(|rule| rule(analyser, stmt, id, symbol));
    }
}

pub mod analyser;
pub mod rules;
