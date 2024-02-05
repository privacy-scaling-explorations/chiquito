use std::fmt::Debug;

use super::{statement::Statement, DebugSymRef};

#[derive(Clone)]
pub enum TLDecl<F, V> {
    MachineDecl {
        dsym: DebugSymRef,
        id: String,
        params: Vec<Statement<F, V>>,
        result: Vec<Statement<F, V>>,
        block: Statement<F, V>,
    },
}

impl<F: Debug, V: Debug> Debug for TLDecl<F, V> {
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
                id,
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
