use std::fmt::Debug;

use super::{expression::Expression, DebugSymRef, Identifiable, Identifier};

/// An identifier with the type it is declared with.
#[derive(Clone)]
pub struct TypedIdDecl<V> {
    /// Identifier
    pub id: V,
    /// type
    pub ty: Option<V>,
}

#[derive(Clone)]
pub enum Statement<F, V> {
    /// assert x;
    Assert(DebugSymRef, Expression<F, V>),
    /// x <-- y;
    SignalAssignment(DebugSymRef, Vec<V>, Vec<Expression<F, V>>),
    /// x <== y;
    SignalAssignmentAssert(DebugSymRef, Vec<V>, Vec<Expression<F, V>>),
    /// x = y;
    WGAssignment(DebugSymRef, Vec<V>, Vec<Expression<F, V>>),
    /// if x { y }
    IfThen(DebugSymRef, Box<Expression<F, V>>, Box<Statement<F, V>>),
    /// if x { y } else { z }
    IfThenElse(
        DebugSymRef,
        Box<Expression<F, V>>,
        Box<Statement<F, V>>,
        Box<Statement<F, V>>,
    ),
    /// signal x;
    SignalDecl(DebugSymRef, Vec<TypedIdDecl<V>>),
    /// var x;
    WGVarDecl(DebugSymRef, Vec<TypedIdDecl<V>>),
    /// state x { y }
    StateDecl(DebugSymRef, V, Box<Statement<F, V>>),
    /// Transition to another state.
    /// -> x { y }
    Transition(DebugSymRef, V, Box<Statement<F, V>>),
    /// { x }
    Block(DebugSymRef, Vec<Statement<F, V>>),
    /// Call into another machine with assertion and subsequent transition to another
    /// state.
    /// Tuple values:
    /// - debug symbol reference;
    /// - assigned signal IDs;
    /// - call expression;
    /// - next state ID;
    HyperTransition(DebugSymRef, Vec<V>, Expression<F, V>, V),
}

impl<F: Debug> Debug for Statement<F, Identifier> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assert(_, arg0) => write!(f, "assert {:?};", arg0),
            Self::SignalAssignment(_, arg0, arg1) => write!(f, "{:?} <-- {:?};", arg0, arg1),
            Self::SignalAssignmentAssert(_, arg0, arg1) => write!(f, "{:?} <== {:?};", arg0, arg1),
            Self::WGAssignment(_, arg0, arg1) => write!(f, "{:?} = {:?};", arg0, arg1),
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
                    .map(|id| id.id.name())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Statement::WGVarDecl(_, id) => write!(
                f,
                "var {};",
                id.iter()
                    .map(|id| id.id.name())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),

            Statement::StateDecl(_, id, stmts) => {
                write!(f, "state {} {:?}", id.name(), stmts)
            }
            Statement::Transition(_, id, stmts) => {
                write!(f, "-> {} {:?}", id.name(), stmts)
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
            Statement::HyperTransition(_, ids, call, state) => {
                write!(
                    f,
                    "{:?} <== {:?} -> {:?};",
                    ids.iter()
                        .map(|id| id.name())
                        .collect::<Vec<_>>()
                        .join(", "),
                    call,
                    state
                )
            }
        }
    }
}

impl<F, V> Statement<F, V> {
    pub fn get_dsym(&self) -> DebugSymRef {
        match self {
            Statement::Assert(dsym, _) => dsym.clone(),
            Statement::SignalAssignment(dsym, _, _) => dsym.clone(),
            Statement::SignalAssignmentAssert(dsym, _, _) => dsym.clone(),
            Statement::WGAssignment(dsym, _, _) => dsym.clone(),
            Statement::IfThen(dsym, _, _) => dsym.clone(),
            Statement::IfThenElse(dsym, _, _, _) => dsym.clone(),
            Statement::SignalDecl(dsym, _) => dsym.clone(),
            Statement::WGVarDecl(dsym, _) => dsym.clone(),
            Statement::StateDecl(dsym, _, _) => dsym.clone(),
            Statement::Transition(dsym, _, _) => dsym.clone(),
            Statement::Block(dsym, _) => dsym.clone(),
            Statement::HyperTransition(dsym, _, _, _) => dsym.clone(),
        }
    }
}
