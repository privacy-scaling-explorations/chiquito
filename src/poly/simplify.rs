use std::hash::Hash;

use crate::field::Field;

use super::Expr;

fn assoc_mul_simplify<F: Field, V: Clone + Eq + PartialEq + Hash>(
    ses: Vec<Expr<F, V>>,
) -> Vec<Expr<F, V>> {
    let mut result: Vec<Expr<F, V>> = Default::default();

    ses.into_iter().for_each(|se| match se {
        Expr::Mul(ses) => result.extend(assoc_mul_simplify(ses)),
        _ => result.push(se),
    });

    result
}

fn const_mul_simplify<F: Field, V: Clone + Eq + PartialEq + Hash>(
    ses: Vec<Expr<F, V>>,
) -> Vec<Expr<F, V>> {
    let mut result: Vec<Expr<F, V>> = Default::default();
    let mut consts: Vec<F> = Default::default();

    ses.into_iter().for_each(|se| match se {
        Expr::Const(v) => consts.push(v),
        _ => result.push(se),
    });

    if consts.is_empty() {
        return result;
    }

    let const_result = consts.into_iter().fold(F::ONE, |acc, v| acc * v);
    result.push(Expr::Const(const_result));

    result
}

pub fn simplify_mul<F: Field, V: Clone + Eq + PartialEq + Hash>(
    ses: Vec<Expr<F, V>>,
) -> Vec<Expr<F, V>> {
    let mut ses = const_mul_simplify(assoc_mul_simplify(ses));
    ses.sort_by_cached_key(|se| se.degree());
    ses
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        poly::{
            simplify::{assoc_mul_simplify, const_mul_simplify, simplify_mul},
            ToExpr,
        },
        sbpir::{query::Queriable, InternalSignal},
    };

    use super::Expr::*;

    #[test]
    fn test_assoc_mul_simplify() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));

        assert_eq!(
            format!(
                "{:#?}",
                Mul(assoc_mul_simplify(vec![a.expr(), 2.expr(), b * 3]))
            ),
            "(a * 0x2 * b * 0x3)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(assoc_mul_simplify(vec![a.expr(), b.expr(), c.expr()]))
            ),
            "(a * b * c)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(assoc_mul_simplify(vec![
                    a.expr(),
                    2.expr(),
                    b * 3,
                    c + (a * 4)
                ]))
            ),
            "(a * 0x2 * b * 0x3 * (c + (a * 0x4)))"
        );
    }

    #[test]
    fn test_const_mul_simplify() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));

        assert_eq!(
            format!(
                "{:#?}",
                Mul(const_mul_simplify(vec![
                    a.expr(),
                    2.expr(),
                    b.expr(),
                    3.expr()
                ]))
            ),
            "(a * b * 0x6)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(assoc_mul_simplify(vec![a.expr(), b.expr(), c.expr()]))
            ),
            "(a * b * c)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(const_mul_simplify(vec![
                    a.expr(),
                    2.expr(),
                    b * 3,
                    c.expr(),
                    a.expr(),
                    4.expr()
                ]))
            ),
            "(a * (b * 0x3) * c * a * 0x8)"
        );
    }

    #[test]
    fn test_simplify_mul() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));

        assert_eq!(
            format!("{:#?}", Mul(simplify_mul(vec![a.expr(), 2.expr(), b * 3]))),
            "(0x6 * a * b)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(simplify_mul(vec![a.expr(), b.expr(), c.expr()]))
            ),
            "(a * b * c)"
        );
        assert_eq!(
            format!(
                "{:#?}",
                Mul(simplify_mul(vec![a.expr(), 2.expr(), b * 3, c + (a * 4)]))
            ),
            "(0x6 * a * b * (c + (a * 0x4)))"
        );
    }
}
