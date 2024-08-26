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

pub fn build_query<F>(id: Identifier, dsym: DebugSymRef) -> Expression<F, Identifier> {
    Expression::Query(dsym, id)
}

pub fn build_identifier<S: Into<String>>(id: S, dsym: DebugSymRef) -> Identifier {
    Identifier::new(id.into(), dsym)
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
