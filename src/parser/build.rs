use num_bigint::BigInt;

use super::ast::{expression::Expression, statement::Statement, DebugSymRef, Identifier};

pub fn build_bin_op<S: Into<String>, F, V>(
    op: S,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
    dsym: DebugSymRef,
) -> Expression<F, V> {
    Expression::BinOp {
        dsym,
        op: op.into().into(),
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn build_unary_op<S: Into<String>, F, V>(
    op: S,
    sub: Expression<F, V>,
    dsym: DebugSymRef,
) -> Expression<F, V> {
    Expression::UnaryOp {
        dsym,
        op: op.into().into(),
        sub: Box::new(sub),
    }
}

pub fn build_query<F>(dsym: DebugSymRef, id: Identifier) -> Expression<F, Identifier> {
    Expression::Query(dsym, id)
}

pub fn build_identifier<S: Into<String>>(id: S) -> Identifier {
    Identifier::from(id.into())
}

pub fn build_assert_eq<F, V>(
    dsym: DebugSymRef,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
) -> Statement<F, V> {
    Statement::Assert(dsym.clone(), build_bin_op("==", lhs, rhs, dsym))
}

pub fn build_assert_neq<F, V>(
    dsym: DebugSymRef,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
) -> Statement<F, V> {
    Statement::Assert(dsym.clone(), build_bin_op("!=", lhs, rhs, dsym))
}

pub fn build_transition_simple<F>(dsym: DebugSymRef, id: Identifier) -> Statement<F, Identifier> {
    Statement::Transition(dsym.clone(), id, Box::new(Statement::Block(dsym, vec![])))
}

pub fn build_transition<F>(
    dsym: DebugSymRef,
    id: Identifier,
    block: Statement<F, Identifier>,
) -> Statement<F, Identifier> {
    Statement::Transition(dsym, id, Box::new(block))
}

pub fn add_dsym(
    dsym: DebugSymRef,
    stmt: Statement<BigInt, Identifier>,
) -> Statement<BigInt, Identifier> {
    match stmt {
        Statement::Assert(_, expr) => Statement::Assert(dsym, expr),
        Statement::SignalAssignment(_, ids, exprs) => Statement::SignalAssignment(dsym, ids, exprs),
        Statement::SignalAssignmentAssert(_, ids, exprs) => {
            Statement::SignalAssignmentAssert(dsym, ids, exprs)
        }
        Statement::WGAssignment(_, ids, exprs) => Statement::WGAssignment(dsym, ids, exprs),
        Statement::StateDecl(_, id, block) => Statement::StateDecl(dsym, id, block),
        Statement::IfThen(_, cond, then_block) => Statement::IfThen(dsym, cond, then_block),
        Statement::IfThenElse(_, cond, then_block, else_block) => {
            Statement::IfThenElse(dsym, cond, then_block, else_block)
        }
        Statement::Block(_, stmts) => Statement::Block(dsym, stmts),
        Statement::SignalDecl(_, ids) => Statement::SignalDecl(dsym, ids),
        Statement::WGVarDecl(_, ids) => Statement::WGVarDecl(dsym, ids),
        Statement::Transition(_, id, stmt) => Statement::Transition(dsym, id, stmt),
    }
}
