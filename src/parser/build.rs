use super::ast::{expression::Expression, statement::Statement, DebugSymRef};

pub fn build_bin_op<S: Into<String>, F, V>(
    op: S,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
) -> Expression<F, V> {
    Expression::BinOp {
        dsym: DebugSymRef::new(0, 0),
        op: op.into().into(),
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn build_unary_op<S: Into<String>, F, V>(op: S, sub: Expression<F, V>) -> Expression<F, V> {
    Expression::UnaryOp {
        dsym: DebugSymRef::new(0, 0),
        op: op.into().into(),
        sub: Box::new(sub),
    }
}

pub fn build_assert_eq<F, V>(
    dsym: DebugSymRef,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
) -> Statement<F, V> {
    Statement::Assert(dsym, build_bin_op("==", lhs, rhs))
}

pub fn build_assert_neq<F, V>(
    dsym: DebugSymRef,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
) -> Statement<F, V> {
    Statement::Assert(dsym, build_bin_op("!=", lhs, rhs))
}
