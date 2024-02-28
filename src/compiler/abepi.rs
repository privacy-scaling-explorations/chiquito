/// Arbitrary boolean expression to Polynomial Identity compiler
use std::marker::PhantomData;

use crate::{
    parser::ast::{
        expression::{BinaryOperator, Expression},
        statement::Statement,
        DebugSymRef,
    },
    poly::Expr,
};

/// Result of compiling an arbitrary boolean expression into a PI
pub struct CompilationResult<F, V> {
    #[allow(dead_code)]
    dsym: DebugSymRef,
    // 0 is true, !=0 is false
    anti_booly: Expr<F, V>,
    // 1 is true, 0 is false, other values are invalid
    one_zero: Expr<F, V>,
}

/// CompilationUnit for ABE to PI
// In the future this will include configuration of the cost function for PI.
pub struct CompilationUnit<F, V> {
    _p: PhantomData<(F, V)>,
}

impl<F, V> Default for CompilationUnit<F, V> {
    fn default() -> Self {
        Self { _p: PhantomData }
    }
}

impl<F: From<u64> + Into<u32> + Clone, V: Clone> CompilationUnit<F, V> {
    pub fn compile_statement(&self, source: Statement<F, V>) -> Vec<CompilationResult<F, V>> {
        match source {
            Statement::Assert(_, expr) => vec![self.compile_expression(expr)],
            Statement::AssignmentAssert(dsym, lhs, rhs) => {
                assert_eq!(lhs.len(), rhs.len());

                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(lhs, rhs)| {
                        self.compile_expression_eq(
                            dsym.clone(),
                            Expression::Query(dsym.clone(), lhs.clone()),
                            rhs.clone(),
                        )
                    })
                    .collect()
            }
            Statement::IfThen(dsym, cond, when_true) => {
                self.compile_statement_if_then(dsym, *cond, *when_true)
            }
            Statement::IfThenElse(dsym, cond, when_true, when_false) => {
                self.compile_statement_if_then_else(dsym, *cond, *when_true, *when_false)
            }
            Statement::Block(_, stmts) => stmts
                .into_iter()
                .flat_map(|stmt| self.compile_statement(stmt))
                .collect(),
            _ => vec![],
        }
    }

    pub fn compile_expression(&self, source: Expression<F, V>) -> CompilationResult<F, V> {
        assert!(source.is_logic());

        self.compile_expression_logic(source)
    }

    fn compile_expression_logic(&self, source: Expression<F, V>) -> CompilationResult<F, V> {
        use crate::parser::ast::expression::{BinaryOperator::*, Expression::*, UnaryOperator::*};
        match source {
            BinOp {
                dsym, op, lhs, rhs, ..
            } => match op {
                Eq => self.compile_expression_eq(dsym, *lhs, *rhs),
                NEq => self.compile_expression_neq(dsym, *lhs, *rhs),
                And => self.compile_expression_and(dsym, *lhs, *rhs),
                Or => self.compile_expression_or(dsym, *lhs, *rhs),
                _ => unreachable!(),
            },
            UnaryOp { dsym, op, sub } => match op {
                Not => self.compile_expression_not(dsym, *sub),
                Neg => unreachable!(),
            },
            True(dsym) => self.compile_expression_true(dsym),
            False(dsym) => self.compile_expression_false(dsym),
            _ => unreachable!(),
        }
    }

    fn compile_expression_airth(&self, source: Expression<F, V>) -> Expr<F, V> {
        use crate::parser::ast::expression::{BinaryOperator::*, Expression::*, UnaryOperator::*};

        match source {
            BinOp { op, lhs, rhs, .. } => {
                assert!(lhs.is_arith());
                assert!(rhs.is_arith());

                match op {
                    Sum => {
                        let mut sub = Vec::new();
                        flatten_bin_op(Sum, *lhs, *rhs, &mut sub);

                        Expr::Sum(
                            sub.into_iter()
                                .map(|se| self.compile_expression_airth(se))
                                .collect(),
                        )
                    }
                    Mul => {
                        let mut sub = Vec::new();
                        flatten_bin_op(Mul, *lhs, *rhs, &mut sub);

                        Expr::Mul(
                            sub.into_iter()
                                .map(|se| self.compile_expression_airth(se))
                                .collect(),
                        )
                    }
                    Sub => {
                        let lhs = self.compile_expression_airth(*lhs);
                        let rhs = self.compile_expression_airth(*rhs);

                        Expr::Sum(vec![lhs, Expr::Neg(Box::new(rhs))])
                    }
                    Pow => {
                        let lhs = self.compile_expression_airth(*lhs);
                        let rhs = self.compile_expression_airth(*rhs);

                        if let Expr::Const(exp) = rhs {
                            Expr::Pow(Box::new(lhs), exp.into())
                        } else {
                            // we can only compile constant exponent
                            unreachable!()
                        }
                    }
                    _ => unreachable!(),
                }
            }
            UnaryOp { op, sub, .. } => match op {
                Neg => {
                    assert!(sub.is_arith());
                    let sub = self.compile_expression_airth(*sub);

                    Expr::Neg(Box::new(sub))
                }
                Not => unreachable!(),
            },
            Query(_, v) => Expr::Query(v),
            Const(_, c) => Expr::Const(c),

            Select {
                cond,
                when_true,
                when_false,
                ..
            } => {
                assert!(cond.is_logic());
                assert!(when_true.is_arith());
                assert!(when_false.is_arith());

                let cond = self.compile_expression_logic(*cond);
                let when_true = self.compile_expression_airth(*when_true);
                let when_false = self.compile_expression_airth(*when_false);

                (cond.one_zero.clone() * when_true) + (cond.one_zero.one_minus() * when_false)
            }
            _ => unreachable!(),
        }
    }

    // LOGIC EXPRESSIONS

    fn compile_expression_true(&self, dsym: DebugSymRef) -> CompilationResult<F, V> {
        use Expr::*;

        CompilationResult {
            dsym,
            anti_booly: Const(F::from(0)),
            one_zero: Const(F::from(1)),
        }
    }

    fn compile_expression_false(&self, dsym: DebugSymRef) -> CompilationResult<F, V> {
        use Expr::*;

        CompilationResult {
            dsym,
            anti_booly: Const(F::from(1)), // note any non-zero is true in anti-booly
            one_zero: Const(F::from(0)),
        }
    }

    fn compile_expression_eq(
        &self,
        dsym: DebugSymRef,
        lhs: Expression<F, V>,
        rhs: Expression<F, V>,
    ) -> CompilationResult<F, V> {
        assert!(lhs.is_arith());
        assert!(rhs.is_arith());

        let lhs = self.compile_expression_airth(lhs);
        let rhs = self.compile_expression_airth(rhs);

        // In anti-booly 0T >0F
        // lhs == rhs => lhs - rhs == 0T; lhs != rhs => lhs - rhs == >0F
        let expr = lhs - rhs;

        CompilationResult {
            dsym,
            anti_booly: expr.clone(),
            one_zero: expr.cast_one_zero(),
        }
    }

    fn compile_expression_neq(
        &self,
        _dsym: DebugSymRef,
        _lhs: Expression<F, V>,
        _rhs: Expression<F, V>,
    ) -> CompilationResult<F, V> {
        assert!(_lhs.is_arith());
        assert!(_rhs.is_arith());

        let lhs = self.compile_expression_airth(_lhs);
        let rhs = self.compile_expression_airth(_rhs);

        // In One Zero: 0 is false, 1 is true
        // lhs != rhs => lhs - rhs != 0
        let expr = lhs - rhs;

        CompilationResult {
            dsym: _dsym,
            anti_booly: expr.clone(),
            one_zero: expr.one_minus(),
        }
    }

    fn compile_expression_and(
        &self,
        dsym: DebugSymRef,
        lhs: Expression<F, V>,
        rhs: Expression<F, V>,
    ) -> CompilationResult<F, V> {
        let mut sub = Vec::new();

        flatten_bin_op(BinaryOperator::And, lhs, rhs, &mut sub);

        assert!(sub.iter().all(|se| se.is_logic()));

        let sub = sub
            .iter()
            .map(|se| self.compile_expression_logic(se.clone()))
            .collect::<Vec<_>>();

        // In OneZero 0F 1T
        // If a, b, c are 1T => a*b*c = 1T, if any of a,b,c is 0F => a*b*c = 0F
        let one_zero = sub
            .iter()
            .skip(1)
            .fold(sub[0].one_zero.clone(), |acc, se| acc * se.one_zero.clone());
        // TODO: the anti_booly version of AND could be split in seveal PIs
        let anti_booly = one_zero.cast_anti_booly();

        CompilationResult {
            dsym,
            anti_booly,
            one_zero,
        }
    }

    fn compile_expression_or(
        &self,
        dsym: DebugSymRef,
        lhs: Expression<F, V>,
        rhs: Expression<F, V>,
    ) -> CompilationResult<F, V> {
        let mut sub = Vec::new();

        flatten_bin_op(BinaryOperator::Or, lhs, rhs, &mut sub);
        assert!(sub.iter().all(|se| se.is_logic()));

        let sub = sub
            .iter()
            .map(|se| self.compile_expression_logic(se.clone()))
            .collect::<Vec<_>>();

        // By De Morgan's law, a or b = not (not a and not b)
        // In OneZero 0F 1T
        // If !a, !b are 1T => !a * !b = 1T, if any of !a, !b is 0F => !a * !b = 0F => (1-a) * (1-b)
        // = 0F So we can do the AND of the negated expressions
        // And then negate the result
        let one_zero = sub
            .iter()
            .skip(1)
            .fold(sub[0].one_zero.clone().one_minus(), |acc, se| {
                acc * se.one_zero.clone().one_minus()
            });

        CompilationResult {
            dsym,
            anti_booly: one_zero.clone(),
            one_zero: one_zero.one_minus(),
        }
    }

    fn compile_expression_not(
        &self,
        dsym: DebugSymRef,
        sub: Expression<F, V>,
    ) -> CompilationResult<F, V> {
        assert!(sub.is_logic());

        let sub = self.compile_expression_logic(sub);

        CompilationResult {
            dsym,
            anti_booly: sub.one_zero.clone(),   // 0F -> 0T, 1T -> 1F
            one_zero: sub.one_zero.one_minus(), // 1T -> 0F, 0F -> 1T
        }
    }

    // STATEMENTS
    fn compile_statement_if_then(
        &self,
        dsym: DebugSymRef,
        cond: Expression<F, V>,
        when_true: Statement<F, V>,
    ) -> Vec<CompilationResult<F, V>> {
        assert!(cond.is_logic());

        let cond = self.compile_expression(cond);

        // if A then assert B
        // not A or B
        // not (A and not B)

        // Using cond only as OneZero 0F, 1T
        // For the OneZero result, only when cond 1T and when_true.one_zero is 0F, 1 - (cond *
        // (1-when_true.one_zero) => 0F, will be 1T in any other case
        // For the AntiBooly result, only when cond 1T and when_true.anti_bool is >0F, cond *
        // when_true.anti_booly => >0F, will be 0F in any other case
        self.compile_statement(when_true)
            .iter()
            .map(|when_true| {
                let one_zero =
                    (cond.one_zero.clone() * when_true.one_zero.clone().one_minus()).one_minus();
                let anti_booly = cond.one_zero.clone() * when_true.anti_booly.clone();

                CompilationResult {
                    dsym: dsym.clone(),
                    anti_booly,
                    one_zero,
                }
            })
            .collect()
    }

    fn compile_statement_if_then_else(
        &self,
        _dsym: DebugSymRef,
        cond: Expression<F, V>,
        _when_true: Statement<F, V>,
        _when_false: Statement<F, V>,
    ) -> Vec<CompilationResult<F, V>> {
        assert!(cond.is_logic());

        let _cond = self.compile_expression(cond);

        // if A then assert B else assert C
        // (A and B) or (not A and C)

        // In OneZero 0F 1T
        // Using cond only as OneZero 0F, 1T
        // For OneZero result =>
        todo!()
    }
}

fn flatten_bin_op<F: Clone, V: Clone>(
    op_: BinaryOperator,
    lhs: Expression<F, V>,
    rhs: Expression<F, V>,
    sub: &mut Vec<Expression<F, V>>,
) {
    if let Expression::BinOp { op, lhs, rhs, .. } = lhs.clone() && op == op_ {
        flatten_bin_op(op, *lhs, *rhs, sub);
    } else {
        sub.push(lhs);
    }
    if let Expression::BinOp { op, lhs, rhs, .. } = rhs.clone() && op == op_ {
        flatten_bin_op(op, *lhs, *rhs, sub);
    } else {
        sub.push(rhs);
    }
}
