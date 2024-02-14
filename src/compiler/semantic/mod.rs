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

#[derive(Clone, Debug)]
pub enum ScopeCategory {
    Global,
    Machine,
    State,
}

#[derive(Clone, Debug)]
pub struct SymTableEntry {
    definition_ref: DebugSymRef,
    category: SymbolCategory,
    ty: Option<String>,
}

impl SymTableEntry {
    fn is_scoped(&self) -> bool {
        matches!(
            self.category,
            SymbolCategory::Machine | SymbolCategory::State
        )
    }
}

pub struct FoundSymbol {
    symbol: SymTableEntry,
    scope: ScopeCategory,
    level: usize,
}

#[derive(Clone)]
pub struct NamespaceTable {
    symbols: HashMap<String, SymTableEntry>,
    scope: ScopeCategory,
}

impl Default for NamespaceTable {
    fn default() -> Self {
        Self {
            symbols: HashMap::default(),
            scope: ScopeCategory::Global,
        }
    }
}

impl Debug for NamespaceTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbols = self
            .symbols
            .keys()
            .sorted()
            .map(|id| format!("\"{}\": {:?}", id, self.symbols[id]))
            .collect::<Vec<_>>()
            .join(",");

        f.debug_struct("NamespaceTable")
            .field("symbols", &symbols)
            .field("scope", &self.scope)
            .finish()
    }
}

impl From<SymTableEntry> for NamespaceTable {
    fn from(entry: SymTableEntry) -> Self {
        NamespaceTable {
            symbols: HashMap::default(),
            scope: match entry.category {
                SymbolCategory::Machine => ScopeCategory::Machine,
                SymbolCategory::State => ScopeCategory::State,
                _ => unreachable!(), // Other symbols don't have their own symbol table
            },
        }
    }
}

impl NamespaceTable {
    fn get_symbol(&self, id: String) -> Option<&SymTableEntry> {
        self.symbols.get(&id)
    }

    fn add_symbol(&mut self, id: String, entry: SymTableEntry) {
        self.symbols.insert(id, entry);
    }
}

#[derive(Default)]
pub struct SymTable {
    namespaces: HashMap<String, NamespaceTable>,
}

impl Display for SymTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .namespaces
            .iter()
            .fold("".to_string(), |acc, (ns, table)| {
                format!("{}{}\n  {:?}\n", acc, ns, table)
            });

        write!(f, "{}", result)
    }
}

impl Debug for SymTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .namespaces
            .keys()
            .sorted()
            .map(|ns| format!("\"{}\": {:?}", ns, self.namespaces[ns]))
            .collect::<Vec<_>>()
            .join(",");

        write!(f, "{}", result)
    }
}

impl SymTable {
    pub fn get_symbol(&self, ns: &[String], id: String) -> Option<&SymTableEntry> {
        self.namespaces
            .get(&Self::get_key(ns))
            .expect("namespace not found")
            .get_symbol(id)
    }

    pub fn find_symbol(&self, ns: &Vec<String>, id: String) -> Option<FoundSymbol> {
        let mut level = 0;
        while level < ns.len() {
            let table = self
                .namespaces
                .get(&Self::get_key_level(ns, level))
                .expect("namespace not found");
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

    pub fn add_symbol(&mut self, ns: &[String], id: String, entry: SymTableEntry) {
        let ns_key = Self::get_key(ns);
        self.namespaces
            .get_mut(&ns_key)
            .unwrap_or_else(|| panic!("namespace {} not found", &ns_key))
            .add_symbol(id.clone(), entry.clone());

        if entry.is_scoped() {
            self.namespaces
                .insert(format!("{}/{}", &ns_key, id), NamespaceTable::from(entry));
        }
    }

    pub fn add_output_variable(&mut self, ns: &[String], id: String, mut entry: SymTableEntry) {
        let prev_symbol = self.get_symbol(ns, id.clone());
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

        self.add_symbol(ns, id, entry);
    }

    fn get_key(ns: &[String]) -> String {
        ns.join("/")
    }

    fn get_key_level(ns: &[String], level: usize) -> String {
        if level == 0 {
            Self::get_key(ns)
        } else {
            ns.iter()
                .rev()
                .skip(level)
                .rev()
                .cloned()
                .collect::<Vec<_>>()
                .join("/")
        }
    }
}

#[derive(Debug)]
pub enum Message {
    Err { msg: String, dsym: DebugSymRef },
}

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

pub(self) struct RuleSet {
    expression: Vec<ExpressionRule>,
    statement: Vec<StatementRule>,
    new_symbol: Vec<NewSymbolRule>,
    new_tl_symbol: Vec<NewTLSymbolRule>,
}

impl RuleSet {
    pub(self) fn apply_expression(
        &self,
        analyser: &mut Analyser,
        expr: &Expression<BigInt, Identifier>,
    ) {
        self.expression.iter().for_each(|rule| rule(analyser, expr));
    }

    pub(self) fn apply_statement(
        &self,
        analyser: &mut Analyser,
        stmt: &Statement<BigInt, Identifier>,
    ) {
        self.statement.iter().for_each(|rule| rule(analyser, stmt));
    }

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
