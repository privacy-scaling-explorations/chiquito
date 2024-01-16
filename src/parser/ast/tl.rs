use super::{statement::Statement, DebugSymRef};

#[derive(Clone, Debug)]
pub enum TLDecl<F, V> {
    TracerDecl(
        DebugSymRef,
        String,
        Vec<Statement<F, V>>,
        Vec<Statement<F, V>>,
    ),
}
