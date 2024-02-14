use std::fmt::Debug;

use super::{statement::Statement, DebugSymRef, Identifiable, Identifier};

#[derive(Clone)]
pub enum TLDecl<F, V> {
    MachineDecl {
        dsym: DebugSymRef,
        id: V,
        params: Vec<Statement<F, V>>,
        result: Vec<Statement<F, V>>,
        block: Statement<F, V>,
    },
}

impl<F: Debug> Debug for TLDecl<F, Identifier> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MachineDecl {
                id,
                params,
                result,
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
