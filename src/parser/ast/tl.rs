use std::fmt::Debug;

use super::{statement::Statement, DebugSymRef, Identifiable, Identifier};

pub struct AST<F, V>(Vec<TLDecl<F, V>>);

impl<F, V: PartialEq> AST<F, V> {
    pub fn machines_iter_mut(&mut self) -> std::slice::IterMut<TLDecl<F, V>> {
        self.0.iter_mut()
    }

    pub fn find_machine(&self, id_machine: V) -> Option<&TLDecl<F, V>> {
        self.0.iter().find(|tldecl| match tldecl {
            TLDecl::MachineDecl { id, .. } => *id == id_machine,
        })
    }
}

#[derive(Clone)]
pub enum TLDecl<F, V> {
    MachineDecl {
        dsym: DebugSymRef,
        id: V,
        input_params: Vec<Statement<F, V>>,
        output_params: Vec<Statement<F, V>>,
        block: Statement<F, V>,
    },
}

impl<F: Debug> Debug for TLDecl<F, Identifier> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MachineDecl {
                id,
                input_params: params,
                output_params: result,
                block,
                ..
            } => write!(
                f,
                "machine {} ({}) ({}) {:?}",
                id.name(),
                params
                    .iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<_>>()
                    .join(", "),
                result
                    .iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<_>>()
                    .join(", "),
                block
            ),
        }
    }
}

impl<F, V> TLDecl<F, V> {
    pub fn get_dsym(&self) -> DebugSymRef {
        match &self {
            TLDecl::MachineDecl { dsym, .. } => dsym.clone(),
        }
    }
}
