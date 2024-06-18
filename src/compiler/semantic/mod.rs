use std::{
    cmp::min,
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
    pub fn new(
        id: String,
        definition_ref: DebugSymRef,
        category: SymbolCategory,
        ty: Option<String>,
    ) -> Self {
        SymTableEntry {
            id,
            definition_ref,
            usages: Vec::new(),
            category,
            ty,
        }
    }

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

    /// Checks if there is a usage of this entry at the given `offset` in the file `filename`.
    /// Returns its proximity score if found, otherwise `None`.
    fn check_usage_at(&self, filename: &String, offset: usize) -> Option<usize> {
        for usage in &self.usages {
            if let Some(usage_proximity) = usage.proximity_score(filename, offset) {
                return Some(usage_proximity);
            }
        }
        None
    }

    /// Returns the proximity score of the closest usage or definition
    /// to the given `offset` in the file `filename`.
    fn proximity_score(&self, filename: &String, offset: usize) -> Option<usize> {
        let result = min(
            self.definition_ref
                .proximity_score(filename, offset)
                .unwrap_or(usize::MAX),
            self.check_usage_at(filename, offset).unwrap_or(usize::MAX),
        );
        if result == usize::MAX {
            None
        } else {
            Some(result)
        }
    }
}

#[derive(Debug)]
/// Extra information when symbol is found in a scope or a containing scope
pub struct FoundSymbol {
    pub symbol: SymTableEntry,
    pub scope_cat: ScopeCategory,
    pub scope_id: String,
    pub level: usize,
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

    /// Add a `usage` to the symbol `id`, if symbol exists in scope.
    fn add_symbol_usage(&mut self, id: String, usage: DebugSymRef) {
        if let Some(symbol) = self.symbols.get(&id) {
            let mut updated_symbol = symbol.clone();
            updated_symbol.usages.push(usage);
            self.symbols.insert(id, updated_symbol);
        }
    }
}

/// Symbol table for a chiquito program
#[derive(Default, Clone)]
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
        let mut level_rev = 0;
        while level_rev < scope.len() {
            let key = Self::get_key_level(scope, level_rev);
            let table = self.scopes.get(&key);
            if table.is_none() {
                level_rev += 1;
                continue;
            }
            let table = table.unwrap();
            let symbol = table.get_symbol(id.clone());

            if symbol.is_some() {
                return symbol.map(|symbol| FoundSymbol {
                    symbol: symbol.clone(),
                    scope_cat: table.scope.clone(),
                    scope_id: key,
                    level: (scope.len() - level_rev - 1),
                });
            }

            level_rev += 1;
        }

        None
    }

    pub fn get_scope(&self, scope: &[String]) -> Option<&ScopeTable> {
        let scope_key = Self::get_key(scope);

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

    /// Add a usage of a symbol.
    /// The function looks up the parent scopes if symbol is not found in the current scope.
    pub fn add_symbol_usage(&mut self, scope: &[String], id: String, usage: DebugSymRef) {
        if let Some(found_symbol) = self.find_symbol(scope, id) {
            self.scopes
                .get_mut(&found_symbol.scope_id)
                .unwrap()
                .add_symbol_usage(found_symbol.symbol.id, usage);
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

    /// Find a `SymTableEntry` by its byte offset in a file.
    /// The function can be called externally (e.g., from the language server)
    ///
    /// ### Parameters
    /// - `filename`: The name of the file where the symbol is searched.
    /// - `offset`: The byte offset in the file where the symbol is searched.
    /// ### Returns
    /// The `SymTableEntry` that is closest to the offset.
    pub fn find_symbol_by_offset(&self, filename: String, offset: usize) -> Option<SymTableEntry> {
        let mut closest_symbol: Option<SymTableEntry> = None;

        for scope in self.scopes.values() {
            for entry in scope.symbols.values() {
                if let Some(proximity) = entry.proximity_score(&filename, offset) {
                    if closest_symbol.is_none()
                        || proximity
                            < closest_symbol
                                .as_ref()
                                .unwrap()
                                .proximity_score(&filename, offset)
                                .unwrap()
                    {
                        closest_symbol = Some(entry.clone());
                    }
                }
            }
        }

        closest_symbol
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

#[cfg(test)]
mod test {
    use crate::{
        compiler::semantic::SymTableEntry,
        parser::{ast::debug_sym_factory::DebugSymRefFactory, lang},
    };

    #[test]
    fn test_find_usages() {
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

        let debug_sym_factory = DebugSymRefFactory::new("some", circuit);
        let decls = lang::TLDeclsParser::new()
            .parse(&debug_sym_factory, circuit)
            .unwrap();

        let result = crate::compiler::semantic::analyser::analyse(&decls);

        let test_cases = [
            (396, "a"),
            (397, "a"),
            (395, "initial"),
            (398, "initial"),
            (460, "a"),
            (584, "a"),
            (772, "a"),
            (402, "c"),
            (478, "c"),
            (578, "c"),
            (683, "c"),
            (797, "c"),
            (468, "n"),
            (481, "n"),
            (617, "n"),
            (669, "n"),
            (686, "n"),
            (780, "n"),
            (800, "n"),
            (399, "b"),
            (464, "b"),
            (475, "b"),
            (588, "b"),
            (665, "b"),
            (776, "b"),
            (794, "b"),
            (393, "i"),
            (608, "i"),
            (661, "i"),
            (676, "i"),
            (768, "i"),
            (787, "i"),
            (437, "middle"),
            (443, "middle"),
        ];

        for (offset, expected_id) in test_cases {
            let SymTableEntry { id, .. } = result
                .symbols
                .find_symbol_by_offset("some".to_string(), offset)
                .unwrap();
            assert_eq!(id, expected_id);
        }
    }
}
