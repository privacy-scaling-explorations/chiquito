use std::collections::HashMap;

use halo2curves::ff::Field;

use crate::{
    ast::{query::Queriable, ASTExpr, InternalSignal},
    poly::{Expr, ToExpr},
    util::UUID,
};

use super::ir::AExprIR;

pub fn compile<F: Field>(source: &AExprIR<F, Queriable<F>>) -> CompilationResult<F> {
    let mut result = CompilationResult::default();

    result.constr = compile_ir(&mut result, source);

    result
}

fn compile_ir<F: Field>(
    result: &mut CompilationResult<F>,
    source: &AExprIR<F, Queriable<F>>,
) -> Expr<F, Queriable<F>> {
    use Expr::*;

    match source {
        AExprIR::Const(v) => Const(v.clone()),
        AExprIR::Sum(ses) => Sum(compiler_ir_vec(result, ses)),
        AExprIR::Mul(ses) => Mul(compiler_ir_vec(result, ses)),
        AExprIR::Neg(se) => Neg(Box::new(compile_ir(result, se))),
        AExprIR::Pow(se, exp) => Pow(Box::new(compile_ir(result, se)), *exp),
        AExprIR::Query(q) => Query(q.clone()),

        AExprIR::MI(se) => compile_mi(result, se),
    }
}

fn compiler_ir_vec<F: Field>(
    result: &mut CompilationResult<F>,
    sub_expressions: &Vec<AExprIR<F, Queriable<F>>>,
) -> Vec<ASTExpr<F>> {
    sub_expressions
        .iter()
        .map(|se| compile_ir(result, se))
        .collect()
}

fn compile_mi<F: Field>(
    result: &mut CompilationResult<F>,
    source: &AExprIR<F, Queriable<F>>,
) -> ASTExpr<F> {
    use Expr::*;

    let virtual_signal = Queriable::Internal(InternalSignal::new("virtual signal".to_string()));
    let virtual_eval_inverse = compile_ir(result, source);
    let virtual_constr = Mul(vec![
        virtual_eval_inverse.clone(),
        Sum(vec![
            Const(F::ONE),
            Neg(Box::new(Mul(vec![
                virtual_eval_inverse.clone(),
                virtual_signal.expr(),
            ]))),
        ]),
    ]);

    result.virtual_queriables.push(virtual_signal);
    result
        .virtual_assign_inv
        .insert(virtual_signal.uuid(), virtual_eval_inverse);
    result.virtual_constr.push(virtual_constr);

    virtual_signal.expr()
}

#[derive(Debug)]
pub struct CompilationResult<F> {
    constr: ASTExpr<F>,
    virtual_constr: Vec<ASTExpr<F>>,
    virtual_queriables: Vec<Queriable<F>>,
    virtual_assign_inv: HashMap<UUID, ASTExpr<F>>,
}

impl<F: Field> Default for CompilationResult<F> {
    fn default() -> Self {
        Self {
            constr: Expr::Const(F::ZERO),
            virtual_constr: Default::default(),
            virtual_queriables: Default::default(),
            virtual_assign_inv: Default::default(),
        }
    }
}

#[cfg(test)]
mod test {

    use std::vec;

    use halo2curves::bn256::Fr;

    use crate::{
        aexpr::ir::AExprIR::*,
        ast::{query::Queriable, InternalSignal},
    };

    use super::compile;

    #[test]
    fn test_simple_aexpr() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a".to_string()));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b".to_string()));

        let input = Mul(vec![
            Query(a),
            MI(Box::new(Sum(vec![Query(b), Const(Fr::from(10))]))),
        ]);

        println!("{:#?}", compile(&input));
    }
}
