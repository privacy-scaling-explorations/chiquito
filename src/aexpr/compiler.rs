use std::{marker::PhantomData, vec};

use crate::aexpr::AExpr;

use super::ir::{AExprIR, CostConfig};

pub fn compile<F: Clone + From<u64>, V: Clone>(
    input: &AExpr<F, V>,
    cost_config: CostConfig,
) -> AExprIR<F, V> {
    let unit = CompilationUnit::new(cost_config);

    unit.compile_logic(input).get_anti_booly()
}

struct CompilationResult<F, V> {
    anti_booly: AExprIR<F, V>,
    one_zero: AExprIR<F, V>,
}

impl<F: Clone, V: Clone> CompilationResult<F, V> {
    fn new(anti_booly: AExprIR<F, V>, one_zero: AExprIR<F, V>) -> Self {
        Self {
            anti_booly,
            one_zero,
        }
    }

    fn get_anti_booly(&self) -> AExprIR<F, V> {
        self.anti_booly.clone()
    }

    fn get_one_zero(&self) -> AExprIR<F, V> {
        self.one_zero.clone()
    }
}

struct CompilationUnit<F, V> {
    cost_config: CostConfig,

    _p: PhantomData<(F, V)>,
}

impl<F: Clone + From<u64>, V: Clone> CompilationUnit<F, V> {
    fn new(cost_config: CostConfig) -> Self {
        CompilationUnit {
            cost_config,
            _p: PhantomData,
        }
    }

    fn compile_logic(&self, input: &AExpr<F, V>) -> CompilationResult<F, V> {
        if input.is_arith() {
            panic!("expected logic expression");
        }

        use AExprIR::*;

        match input {
            // We are assuming variables in logical expressions are OneZero
            AExpr::Query(q) => {
                CompilationResult::new(Query(q.clone()).cast_anti_booly(), Query(q.clone()))
            }

            AExpr::Eq(lhs, rhs) => {
                self.compile_eq(self.compile_arith(lhs), self.compile_arith(rhs))
            }
            AExpr::NEq(lhs, rhs) => {
                self.compile_neq(self.compile_arith(lhs), self.compile_arith(rhs))
            }
            AExpr::And(se) => self.compile_and(self.compile_logic_vec(se)),
            AExpr::Or(se) => self.compile_or(self.compile_logic_vec(se)),
            AExpr::Not(expr) => self.compile_not(self.compile_logic(expr)),
            AExpr::IfThen(selector, when_true) => {
                self.compile_if_then(self.compile_logic(selector), self.compile_logic(when_true))
            }
            AExpr::IfThenElse(selector, when_true, when_false) => self.compile_if_then_else(
                self.compile_logic(selector),
                self.compile_logic(when_true),
                self.compile_logic(when_false),
            ),

            _ => unreachable!(),
        }
    }

    fn compile_arith(&self, input: &AExpr<F, V>) -> AExprIR<F, V> {
        use AExprIR::*;

        match input {
            AExpr::Const(c) => Const(c.clone()),
            AExpr::Sum(es) => Sum(self.compile_arith_vec(es)),
            AExpr::Mul(es) => Mul(self.compile_arith_vec(es)),
            AExpr::Neg(e) => Neg(Box::new(self.compile_arith(e))),
            AExpr::Pow(e, exp) => Pow(Box::new(self.compile_arith(e)), *exp),
            AExpr::Query(q) => Query(q.clone()),
            AExpr::Select(selector, when_true, when_false) => self.compile_select(self.compile_logic(selector), self.compile_arith(when_true), self.compile_arith(when_false)),

            _ => panic!("arithmetic expression expected"),
        }
    }

    fn compile_arith_vec(&self, input: &Vec<AExpr<F, V>>) -> Vec<AExprIR<F, V>> {
        input.into_iter().map(|e| self.compile_arith(e)).collect()
    }

    fn compile_logic_vec(&self, input: &Vec<AExpr<F, V>>) -> Vec<CompilationResult<F, V>> {
        input.into_iter().map(|e| self.compile_logic(e)).collect()
    }

    fn compile_eq(&self, lhs: AExprIR<F, V>, rhs: AExprIR<F, V>) -> CompilationResult<F, V> {
        use AExprIR::*;

        let expr = Sum(vec![lhs, Neg(Box::new(rhs))]);

        CompilationResult::new(expr.clone(), expr.cast_one_zero())
    }

    fn compile_neq(&self, lhs: AExprIR<F, V>, rhs: AExprIR<F, V>) -> CompilationResult<F, V> {
        use AExprIR::*;

        // neq anti-booly, 0 if they are not equal, >0 if they are equal (1- (lhs - rhs))
        // one_zero, 1 if they are not equal, 0 if they are equal (lhs-rhs)
        let expr = Sum(vec![lhs, Neg(Box::new(rhs))]);

        CompilationResult::new(expr.cast_anti_booly(), expr)
    }

    fn compile_not(&self, expr: CompilationResult<F, V>) -> CompilationResult<F, V> {
        let (anti_booly_sub, one_zero_sub) = (expr.get_anti_booly(), expr.get_one_zero());

        // anti_booly
        // T - 0
        // F - > 0
        // not(e)
        // e anti_booly
        // 0_T -> >0_F
        // >0_F -> 0_T
        // not(e) = is_zero(e)
        // e OZ
        // 1 -> 1
        // 0 -> 0
        // not(e) = e
        let anti_booly = one_zero_sub;

        // OZ
        // T -> 1
        // F -> 0
        // not(e)
        // e anti_booly
        // 0_T -> 0_F
        // >0_F -> 1_T
        // not(e) = e
        // e OZ
        // 0_F -> 1_T
        // 1_T -> 0_F
        // not(e) = 1 - e
        let one_zero = anti_booly_sub;

        CompilationResult::new(anti_booly, one_zero)
    }

    fn compile_and(
        &self,
        sub_expressions: Vec<CompilationResult<F, V>>,
    ) -> CompilationResult<F, V> {
        use AExprIR::*;

        // AntiBooly and (AntiBooly operands)
        // a + b + c -> if any operand is >0_F , then result >0_F; If all are 0_T, then result 0_T
        let anti_booly = Sum(sub_expressions
            .iter()
            .map(|se| se.get_anti_booly())
            .collect());

        // OneZero and (OneZero operands)
        // a * b * c -> if any operand is 0_F, then result 0_F; If all are 1_T, then result 1_T
        let one_zero = Mul(sub_expressions.iter().map(|se| se.get_one_zero()).collect());

        self.get_best(CompilationResult::new(anti_booly, one_zero))
    }

    fn compile_or(&self, sub_expressions: Vec<CompilationResult<F, V>>) -> CompilationResult<F, V> {
        use AExprIR::*;

        // AntiBooly or (AntiBooly operands)
        // a * b * c -> if one operand is 0_T , then result is 0_T; If all are 0>_F, then result
        // 0>_F
        let anti_booly = Mul(sub_expressions
            .iter()
            .map(|se| se.get_anti_booly())
            .collect());

        // OneZero and (OneZero operands)
        // 1 - ((1-a) * (1-b) * (1-c)) -> if one operand is 1_T, then result 1_T; If all are 0_F,
        // then result 0_F
        let one_zero =
            Mul(sub_expressions.iter().map(|se| se.get_one_zero()).collect()).one_minus();

        self.get_best(CompilationResult::new(anti_booly, one_zero))
    }

    fn compile_if_then(
        &self,
        selector: CompilationResult<F, V>,
        when_true: CompilationResult<F, V>,
    ) -> CompilationResult<F, V> {
        use AExprIR::*;

        // selector true => when_true
        // selector false => true

        let anti_booly = Mul(vec![selector.get_one_zero(), when_true.get_anti_booly()]);

        let one_zero = anti_booly.cast_one_zero();

        CompilationResult::new(anti_booly, one_zero)
    }

    fn compile_if_then_else(
        &self,
        selector: CompilationResult<F, V>,
        when_true: CompilationResult<F, V>,
        when_false: CompilationResult<F, V>,
    ) -> CompilationResult<F, V> {
        use AExprIR::*;
        let anti_booly = Sum(vec![
            Mul(vec![selector.get_one_zero(), when_true.get_anti_booly()]),
            Mul(vec![
                selector.get_one_zero().one_minus(),
                when_false.get_anti_booly(),
            ]),
        ]);

        let one_zero = anti_booly.cast_one_zero();

        CompilationResult::new(anti_booly, one_zero)
    }

    fn compile_select(
        &self,
        selector: CompilationResult<F, V>,
        when_true: AExprIR<F, V>,
        when_false: AExprIR<F, V>,
    ) -> AExprIR<F, V> {
        use AExprIR::*;

        Sum(vec![
            Mul(vec![selector.get_one_zero(), when_true]),
            Mul(vec![selector.get_one_zero().one_minus(), when_false]),
        ])
    }

    fn cost(&self, expr: &AExprIR<F, V>) -> u64 {
        expr.cost(&self.cost_config)
    }

    fn choose_min_expr(&self, exprs: Vec<AExprIR<F, V>>) -> AExprIR<F, V> {
        let mut min_cost = self.cost(&exprs[0]);
        let mut min_expr = exprs[0].clone();
        for expr in exprs.iter().skip(1) {
            let cost = self.cost(&expr);
            if cost < min_cost {
                min_cost = cost;
                min_expr = expr.clone();
            }
        }

        min_expr
    }

    fn get_best(&self, cr: CompilationResult<F, V>) -> CompilationResult<F, V> {
        CompilationResult::new(
            self.choose_min_expr(vec![
                cr.get_anti_booly(),
                cr.get_one_zero().cast_anti_booly(),
            ]),
            self.choose_min_expr(vec![cr.get_anti_booly().cast_one_zero(), cr.get_one_zero()]),
        )
    }
}
