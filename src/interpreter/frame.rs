use std::{collections::HashMap, hash::Hash};

use crate::{
    compiler::semantic::{FoundSymbol, SymTable},
    field::Field,
    parser::ast::Identifiable,
    sbpir::query::Queriable,
    wit_gen::{StepInstance, SymbolSignalMapping},
};

use super::value::Value;

#[derive(Default, Debug)]
pub(super) struct StackFrameScope<F: Field> {
    lex_scope: String,
    signals: [HashMap<String, Value<F>>; 2],
    variables: HashMap<String, Value<F>>,
}

impl<F: Field + Hash> StackFrameScope<F> {
    fn new(lex_scope: String) -> Self {
        Self {
            lex_scope,
            ..StackFrameScope::default()
        }
    }

    fn get_value<V: Identifiable>(&self, id: &V) -> Option<&Value<F>> {
        if id.rotation() == 0 {
            self.signals[0]
                .get(&id.name())
                .or(self.variables.get(&id.name()))
        } else if id.rotation() == 1 {
            self.signals[1].get(&id.name())
        } else {
            unreachable!("semantic fail");
        }
    }

    fn set_value<V: Identifiable>(&mut self, id: &V, symbol: &FoundSymbol, value: &Value<F>) {
        if symbol.symbol.is_signal() {
            // TODO: should we check here that if rotation == 1 it is a shared signal?
            self.signals[id.rotation() as usize].insert(id.name(), *value);
        } else {
            self.variables.insert(id.name(), *value);
        }
    }

    fn get_all_signals_values(&self, mapping: &SymbolSignalMapping) -> HashMap<Queriable<F>, F> {
        let mut result: HashMap<Queriable<F>, F> = HashMap::default();

        for (id, value) in self.signals[0].iter() {
            let q = mapping.get_queriable::<F>(&self.lex_scope, id, false);

            result.insert(q, value.unwrap());
        }

        result
    }
}

#[derive(Debug)]
pub(super) struct StackFrame<'a, F: Field> {
    symbols: &'a SymTable,
    lex_scope: Vec<String>,

    scopes: Vec<StackFrameScope<F>>,
    cur_machine: String,
    cur_state: String,
}

impl<'a, F: Field + Hash> StackFrame<'a, F> {
    pub(super) fn new(symbols: &'a SymTable) -> Self {
        Self {
            symbols,
            lex_scope: vec!["/".to_string()],
            scopes: vec![],
            cur_machine: String::default(),
            cur_state: String::default(),
        }
    }

    pub(super) fn get_state(&self) -> String {
        self.cur_state.clone()
    }

    pub(super) fn get_value<V: Identifiable>(&self, id: &V) -> Option<&Value<F>> {
        let mut value = None;
        for scope in self.scopes.iter().rev() {
            value = scope.get_value(id);
            if value.is_some() {
                break;
            }
        }

        value
    }

    pub(super) fn set_value<V: Identifiable>(&mut self, id: &V, value: &Value<F>) {
        let symbol = self
            .symbols
            .find_symbol(&self.lex_scope, id.name())
            .expect("semantic fail");

        self.scopes[symbol.level - 1].set_value(id, &symbol, value);
    }

    pub(super) fn enter_machine<S: Into<String>>(&mut self, machine_id: S) {
        self.cur_machine = machine_id.into();
        self.lex_scope.push(self.cur_machine.clone());
        self.scopes
            .push(StackFrameScope::new(self.lex_scope.join("/")));

        self.enter_state("initial");
    }

    fn enter_state<S: Into<String>>(&mut self, next_state: S) {
        self.cur_state = next_state.into();
        self.lex_scope.push(self.cur_state.clone());
        self.scopes
            .push(StackFrameScope::new(self.lex_scope.join("/")));
    }

    fn exit_state(&mut self) {
        self.lex_scope.pop();
        self.scopes.pop();
    }

    pub(super) fn state_transition(
        &mut self,
        mapping: &SymbolSignalMapping,
        next_state: &Option<String>,
    ) -> StepInstance<F> {
        let mut assignments: HashMap<Queriable<F>, F> =
            self.scopes[1].get_all_signals_values(mapping);
        assignments.extend(self.scopes[0].get_all_signals_values(mapping));

        let step_type_uuid = mapping
            .get_step_type_handler(&self.cur_machine, &self.cur_state)
            .uuid();

        let step_instance: StepInstance<F> = StepInstance {
            step_type_uuid,
            assignments,
        };

        self.exit_state();

        self.scopes[0].signals[0] = self.scopes[0].signals[1].clone();
        self.scopes[0].signals[1].clear();

        if next_state.is_some() {
            self.enter_state(next_state.clone().unwrap());
        } else if !self.scopes[0].signals[0].is_empty() {
            panic!("final state put values in next step");
        }

        step_instance
    }
}
