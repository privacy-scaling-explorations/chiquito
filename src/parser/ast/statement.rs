use std::fmt::Debug;

use super::{expression::Expression, DebugSymRef};

#[derive(Clone)]
pub enum Statement<F, V> {
    Assert(DebugSymRef, Expression<F, V>),
    Assignment(DebugSymRef, V, Expression<F, V>),
    AssignmentAssert(DebugSymRef, V, Expression<F, V>),

    IfThen(DebugSymRef, Box<Expression<F, V>>, Vec<Statement<F, V>>),
    IfThenElse(
        DebugSymRef,
        Box<Expression<F, V>>,
        Vec<Statement<F, V>>,
        Vec<Statement<F, V>>,
    ),

    SignalDecl(DebugSymRef, String),
    ForwardSignalDecl(DebugSymRef, String),
    InternalSignalDecl(DebugSymRef, String),
    VarDecl(DebugSymRef, String),

    StepTypeDecl(
        DebugSymRef,
        String,
        Vec<Statement<F, V>>,
        Vec<Statement<F, V>>,
    ),
}

impl<F: Debug, V: Debug> Debug for Statement<F, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assert(_, arg0) => write!(f, "assert {:?};", arg0),
            Self::Assignment(_, arg0, arg1) => write!(f, "{:?} <-- {:?};", arg0, arg1),
            Self::AssignmentAssert(_, arg0, arg1) => write!(f, "{:?} <== {:?};", arg0, arg1),
            Statement::IfThen(_, arg0, arg1) => write!(
                f,
                "if {:?} then {{\n {}\n}}\n",
                arg0,
                arg1.iter()
                    .map(|e| format!("{:?}", e))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Statement::IfThenElse(_, arg0, arg1, arg2) => write!(
                f,
                "if {:?} then {{\n {}\n}} else{{\n {}\n}} \n",
                arg0,
                arg1.iter()
                    .map(|e| format!("{:?}", e))
                    .collect::<Vec<_>>()
                    .join(" "),
                arg2.iter()
                    .map(|e| format!("{:?}", e))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),

            Statement::SignalDecl(_, id) => write!(f, "signal {};", id),
            Statement::ForwardSignalDecl(_, _) => todo!(),
            Statement::InternalSignalDecl(_, _) => todo!(),
            Statement::VarDecl(_, id) => write!(f, "var {};", id),

            Statement::StepTypeDecl(_, id, params, stmts) => {
                write!(f, "step {}({:?}) {{ {:?} }}", id, params, stmts)
            }
        }
    }
}
