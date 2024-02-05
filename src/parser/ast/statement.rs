use std::fmt::Debug;

use super::{expression::Expression, DebugSymRef};

/// An identifier with the type it is declared with.
#[derive(Clone)]
pub struct TypedIdDecl {
    /// Identifier
    pub id: String,
    /// type
    pub ty: Option<String>,
}

#[derive(Clone)]
pub enum Statement<F, V> {
    Assert(DebugSymRef, Expression<F, V>),

    Assignment(DebugSymRef, Vec<V>, Vec<Expression<F, V>>),
    AssignmentAssert(DebugSymRef, Vec<V>, Vec<Expression<F, V>>),

    IfThen(DebugSymRef, Box<Expression<F, V>>, Box<Statement<F, V>>),
    IfThenElse(
        DebugSymRef,
        Box<Expression<F, V>>,
        Box<Statement<F, V>>,
        Box<Statement<F, V>>,
    ),

    SignalDecl(DebugSymRef, Vec<TypedIdDecl>),
    WGVarDecl(DebugSymRef, Vec<TypedIdDecl>),

    StateDecl(DebugSymRef, String, Box<Statement<F, V>>),

    Transition(DebugSymRef, String, Box<Statement<F, V>>),

    Block(DebugSymRef, Vec<Statement<F, V>>),
}

impl<F: Debug, V: Debug> Debug for Statement<F, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assert(_, arg0) => write!(f, "assert {:?};", arg0),
            Self::Assignment(_, arg0, arg1) => write!(f, "{:?} <-- {:?};", arg0, arg1),
            Self::AssignmentAssert(_, arg0, arg1) => write!(f, "{:?} <== {:?};", arg0, arg1),
            Statement::IfThen(_, arg0, arg1) => {
                write!(f, "if {:?} {:?}", arg0, arg1)
            }
            Statement::IfThenElse(_, arg0, arg1, arg2) => {
                write!(f, "if {:?} {:?} else {:?}", arg0, arg1, arg2)
            }

            Statement::SignalDecl(_, id) => write!(
                f,
                "signal {};",
                id.iter()
                    .map(|id| id.id.clone())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Statement::WGVarDecl(_, id) => write!(
                f,
                "var {};",
                id.iter()
                    .map(|id| id.id.clone())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),

            Statement::StateDecl(_, id, stmts) => {
                write!(f, "state {} {:?}", id, stmts)
            }
            Statement::Transition(_, id, stmts) => {
                write!(f, "-> {} {:?}", id, stmts)
            }
            Statement::Block(_, stms) => {
                write!(
                    f,
                    "{{ {} }}",
                    stms.iter()
                        .map(|stm| format!("{:?}", stm))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        }
    }
}
