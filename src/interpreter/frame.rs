use std::{collections::HashMap, hash::Hash};

use crate::{
    compiler::semantic::{FoundSymbol, SymTable},
    field::Field,
    parser::ast::Identifiable,
    sbpir::query::Queriable,
    wit_gen::{StepInstance, SymbolSignalMapping},
};

use super::value::Value;

/// Represents one of the scopes in the execution of one stack frame. At one point a stack frame has
/// one or more nested scopes.
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

    fn transition_signals(&mut self) {
        self.signals[0] = self.signals[1].clone();
        self.signals[1].clear();
    }
}

/// Containts a stack frame of execution.
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

    /// Get state name.
    pub(super) fn get_state(&self) -> String {
        self.cur_state.clone()
    }

    /// Get current value in this stack frame for a variable.
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

    /// Set/changes value for an identifier in this stack frame.
    pub(super) fn set_value<V: Identifiable>(&mut self, id: &V, value: &Value<F>) {
        let symbol = self
            .symbols
            .find_symbol(&self.lex_scope, id.name())
            .expect("semantic fail");

        self.scopes[symbol.level - 1].set_value(id, &symbol, value);
    }

    /// If this stack frame is in a machine, enters the machine and starts it. The execution of a
    /// machine has only one stack frame, the states are inner scopes in the same stack frame.
    pub(super) fn enter_machine<S: Into<String>>(&mut self, machine_id: S) {
        self.cur_machine = machine_id.into();
        self.lex_scope.push(self.cur_machine.clone());
        self.scopes
            .push(StackFrameScope::new(self.lex_scope.join("/")));

        self.enter_state("initial");
    }

    pub(super) fn enter_state<S: Into<String>>(&mut self, next_state: S) {
        self.cur_state = next_state.into();
        self.lex_scope.push(self.cur_state.clone());
        self.scopes
            .push(StackFrameScope::new(self.lex_scope.join("/")));
    }

    fn exit_state(&mut self) {
        self.lex_scope.pop();
        self.scopes.pop();
    }

    /// Transitions to a new state. The scope of the old state is destroyed, and a new one is
    /// created. The values of the forward signals next step are move to current state.
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

        self.scopes[0].transition_signals();

        if next_state.is_some() {
            self.enter_state(next_state.clone().unwrap());
        } else if !self.scopes[0].signals[0].is_empty() {
            panic!("final state put values in next step");
        }

        step_instance
    }
}
