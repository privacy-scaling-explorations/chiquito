use std::hash::Hash;

use num_bigint::BigInt;

use crate::{
    compiler::Message,
    field::Field,
    interpreter::value::Value,
    parser::ast::{
        expression::{BinaryOperator, Expression, UnaryOperator},
        Identifiable,
    },
};

use super::frame::StackFrame;

pub(crate) fn eval_expr<F: Field + Hash, V: Identifiable>(
    frame: &StackFrame<F>,
    expr: &Expression<BigInt, V>,
) -> Result<Value<F>, Message> {
    use BinaryOperator::*;
    use Expression::*;
    use UnaryOperator::*;

    match expr {
        BinOp { op, lhs, rhs, .. } => {
            let lhs = eval_expr(frame, lhs)?;
            let rhs = eval_expr(frame, rhs)?;
            match op {
                Sum => lhs.sum(&rhs),
                Sub => lhs.sub(&rhs),
                Mul => lhs.mul(&rhs),
                Pow => todo!(),
                MulInv => todo!(),
                Div => todo!(),
                DivRem => todo!(),
                RightShift => todo!(),
                LeftShift => todo!(),
                Eq => lhs.eq(&rhs),
                NEq => todo!(),
                Greater => todo!(),
                Less => todo!(),
                GreaterEq => todo!(),
                LessEq => todo!(),
                And => todo!(),
                Or => todo!(),
                BitAnd => todo!(),
                BitOr => todo!(),
                BitXor => todo!(),
            }
        }
        UnaryOp { op, sub, .. } => {
            let sub = eval_expr(frame, sub)?;
            match op {
                Not => todo!(),
                Neg => sub.neg(),
                Complement => todo!(),
            }
        }
        Select {
            cond,
            when_true,
            when_false,
            ..
        } => {
            let cond = eval_expr(frame, cond)?;

            if let Value::Bool(cond) = cond {
                if cond {
                    Ok(eval_expr(frame, when_true)?)
                } else {
                    Ok(eval_expr(frame, when_false)?)
                }
            } else {
                Err("condition in select does not evaluate to boolean".to_string())
            }
        }
        Query(_, id) => frame
            .get_value(id)
            .cloned()
            .ok_or_else(|| format!("value not found for {}", id.name())),
        Const(_, v) => Ok(Value::Field(F::from_big_int(v))),
        True(_) => Ok(Value::Bool(true)),
        False(_) => Ok(Value::Bool(false)),
        Call(_, _, _) => {
            todo!("Needs specs. Evaluate the argument expressions, evaluate the function output?")
        }
    }
    .map_err(|msg| Message::RuntimeErr {
        msg,
        dsym: expr.get_dsym().clone(),
    })
}
