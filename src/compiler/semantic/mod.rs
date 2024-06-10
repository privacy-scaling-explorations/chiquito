use std::{
    collections::{BTreeMap, HashMap},
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

use super::Message;

pub mod analyser;
pub mod rules;

/// Category of a symbol
#[derive(Clone, PartialEq, Debug)]
pub enum SymbolCategory {
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
    pub id: String,
    pub definition_ref: DebugSymRef,
    pub usages: Vec<DebugSymRef>,
    pub category: SymbolCategory,
    /// Type
    pub ty: Option<String>,
}

impl SymTableEntry {
    pub fn is_scoped(&self) -> bool {
        matches!(
            self.category,
            SymbolCategory::Machine | SymbolCategory::State
        )
    }

    pub fn is_signal(&self) -> bool {
        matches!(
            self.category,
            SymbolCategory::Signal
                | SymbolCategory::InputSignal
                | SymbolCategory::OutputSignal
                | SymbolCategory::InoutSignal
        )
    }

    fn get_type(&self) -> &str {
        match &self.ty {
            Some(ty) => ty,
            None => "field",
        }
    }

    fn look_in_usages(
        &self,
        filename: String,
        offset: usize,
        symbols_by_proximity: &mut BTreeMap<i32, SymTableEntry>,
    ) {
        for usage in &self.usages {
            if usage.get_filename() != filename {
                continue;
            }
            let usage_proximity = usage.proximity_score(offset);
            if usage_proximity != -1 {
                symbols_by_proximity.insert(usage_proximity, self.clone());
                break;
            }
        }
    }
}

/// Extra information when symbol is found in a scope or a containing scope
pub struct FoundSymbol {
    pub symbol: SymTableEntry,
    pub scope: ScopeCategory,
    pub level: usize,
    pub usages: Vec<DebugSymRef>,
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

    pub fn get_category(&self) -> ScopeCategory {
        self.scope.clone()
    }

    pub fn get_symbols(&self) -> &HashMap<String, SymTableEntry> {
        &self.symbols
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
            let table = self.scopes.get(&Self::get_key_level(scope, level));
            if table.is_none() {
                level += 1;
                continue;
            }
            let table = table.unwrap();
            let symbol = table.get_symbol(id.clone());

            if symbol.is_some() {
                return symbol.map(|symbol| FoundSymbol {
                    symbol: symbol.clone(),
                    scope: table.scope.clone(),
                    level,
                    usages: symbol.usages.clone(),
                });
            }

            level += 1;
        }

        None
    }

    pub fn get_scope(&self, scope: &[String]) -> Option<&ScopeTable> {
        let scope_key = Self::get_key(scope);
        println!("scope_key: {}", scope_key);

        self.scopes.get(&scope_key)
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

    /// Update usages of a symbol.
    /// The functions looks up the scope if symbol is not found in the current scope.
    pub fn update_usages(&mut self, scope: &[String], id: String, usage: DebugSymRef) {
        let scope_key = Self::get_key(scope);
        let scope_table = &self.scopes.get_mut(&scope_key);
        if let Some(scope_table) = scope_table {
            let existing_symbol = scope_table.get_symbol(id.clone());

            if let Some(existing_symbol) = existing_symbol {
                let mut updated_symbol = existing_symbol.clone();
                updated_symbol.usages.push(usage);
                self.scopes
                    .get_mut(&scope_key)
                    .unwrap()
                    .add_symbol(id.clone(), updated_symbol.clone());
            } else {
                if scope.len() == 1 {
                    return;
                }
                let parent_scope = &scope
                    .iter()
                    .take(scope.len() - 1)
                    .cloned()
                    .collect::<Vec<_>>();
                self.update_usages(parent_scope, id, usage);
            }
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

    pub fn find_symbol_by_offset(&self, filename: String, offset: usize) -> Option<SymTableEntry> {
        let mut symbols_by_proximity = BTreeMap::<i32, SymTableEntry>::new();

        for scope in self.scopes.values() {
            for entry in scope.symbols.values() {
                // If the entry is not in the same file, check its usages
                if entry.definition_ref.get_filename() != filename.clone() {
                    entry.look_in_usages(filename.clone(), offset, &mut symbols_by_proximity);
                } else {
                    let proximity = entry.definition_ref.proximity_score(offset);
                    // If the current entry is not enclosing the offset, check the usages of that
                    // entry
                    if proximity == -1 {
                        entry.look_in_usages(filename.clone(), offset, &mut symbols_by_proximity);
                    // If the current entry is enclosing the offset, add it to the map
                    } else {
                        symbols_by_proximity.insert(proximity, entry.clone());
                    }
                }
            }
        }

        if symbols_by_proximity.is_empty() {
            None
        } else {
            // Return the first symbol in the map because BTreeMap is sorted by the key (which is
            // the proximity in our case)
            return symbols_by_proximity
                .iter()
                .next()
                .map(|(_, entry)| entry.clone());
        }
    }
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
