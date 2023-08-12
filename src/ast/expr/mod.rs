use std::{
    fmt::Debug,
    ops::{Add, Mul, Neg, Sub},
};

use halo2_proofs::{arithmetic::Field, plonk::Expression};

use crate::frontend::dsl::cb::Constraint;

use self::query::Queriable;

pub mod query;

pub trait ToExpr<F> {
    fn expr(&self) -> Expr<F>;
}

pub trait ToField<F> {
    fn field(&self) -> F;
}

#[derive(Clone)]
pub enum Expr<F> {
    Const(F),
    Sum(Vec<Expr<F>>),
    Mul(Vec<Expr<F>>),
    Neg(Box<Expr<F>>),
    Pow(Box<Expr<F>>, u32),
    Query(Queriable<F>),
    Halo2Expr(Expression<F>),
}

impl<F: Debug> Debug for Expr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(arg0) => {
                let formatted = format!("{:?}", arg0);
                if formatted.starts_with("0x") {
                    let s = format!(
                        "0x{}",
                        formatted.trim_start_matches("0x").trim_start_matches('0')
                    );
                    write!(f, "{}", s)
                } else {
                    write!(f, "{}", formatted)
                }
            }
            Self::Sum(arg0) => write!(
                f,
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" + ")
            ),
            Self::Mul(arg0) => write!(
                f,
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" * ")
            ),
            Self::Neg(arg0) => write!(f, "-{:?}", arg0),
            Self::Pow(arg0, arg1) => write!(f, "({:?})^{}", arg0, arg1),
            Self::Query(arg0) => write!(f, "{:?}", arg0),
            Self::Halo2Expr(arg0) => write!(f, "halo2({:?})", arg0),
        }
    }
}

impl<F: Clone> ToExpr<F> for Expr<F> {
    fn expr(&self) -> Expr<F> {
        self.clone()
    }
}

impl<F> From<Constraint<F>> for Expr<F> {
    fn from(c: Constraint<F>) -> Self {
        c.expr
    }
}

impl<F> From<Queriable<F>> for Expr<F> {
    fn from(value: Queriable<F>) -> Self {
        Expr::Query(value)
    }
}

impl<F, RHS: Into<Expr<F>>> Add<RHS> for Expr<F> {
    type Output = Self;
    fn add(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs) => {
                xs.push(rhs.into());
                Sum(xs)
            }
            e => Sum(vec![e, rhs.into()]),
        }
    }
}

impl<F, RHS: Into<Expr<F>>> Sub<RHS> for Expr<F> {
    type Output = Self;
    fn sub(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs) => {
                xs.push(rhs.into().neg());
                Sum(xs)
            }
            e => Sum(vec![e, rhs.into().neg()]),
        }
    }
}

impl<F, RHS: Into<Expr<F>>> Mul<RHS> for Expr<F> {
    type Output = Self;
    fn mul(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Mul(mut xs) => {
                xs.push(rhs.into());
                Mul(xs)
            }
            e => Mul(vec![e, rhs.into()]),
        }
    }
}

impl<F> Neg for Expr<F> {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Expr::Neg(xs) => *xs,
            e => Expr::Neg(Box::new(e)),
        }
    }
}

macro_rules! impl_expr_like {
    ($type:ty) => {
        impl<F: From<u64>> From<$type> for Expr<F> {
            #[inline]
            fn from(value: $type) -> Self {
                Expr::Const(F::from(value as u64))
            }
        }

        impl<F: From<u64>> $crate::ast::ToExpr<F> for $type {
            #[inline]
            fn expr(&self) -> Expr<F> {
                Expr::Const(F::from(*self as u64))
            }
        }

        impl<F: From<u64>> $crate::ast::ToField<F> for $type {
            #[inline]
            fn field(&self) -> F {
                F::from(*self as u64)
            }
        }
    };
}

impl_expr_like!(bool);
impl_expr_like!(u8);
impl_expr_like!(u32);
impl_expr_like!(u64);
impl_expr_like!(usize);

impl<F: Field + From<u64>> From<i32> for Expr<F> {
    #[inline]
    fn from(value: i32) -> Self {
        Expr::Const(
            F::from(value.unsigned_abs() as u64)
                * if value.is_negative() { -F::ONE } else { F::ONE },
        )
    }
}

impl<F: Field + From<u64>> ToExpr<F> for i32 {
    #[inline]
    fn expr(&self) -> Expr<F> {
        Expr::Const(
            F::from(self.unsigned_abs() as u64) * if self.is_negative() { -F::ONE } else { F::ONE },
        )
    }
}

impl<F: Field + From<u64>> ToField<F> for i32 {
    #[inline]
    fn field(&self) -> F {
        F::from(self.unsigned_abs() as u64) * if self.is_negative() { -F::ONE } else { F::ONE }
    }
}

impl<F> From<Expression<F>> for Expr<F> {
    #[inline]
    fn from(value: Expression<F>) -> Self {
        Expr::Halo2Expr(value)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_expr_fmt() {
        let a: Fr = 10.into();
        let b: Fr = 20.into();

        let expr1 = Expr::Const(&a);
        assert_eq!(format!("{:?}", expr1), "0xa");

        let expr2 = Expr::Sum(vec![Expr::Const(&a), Expr::Const(&b)]);
        assert_eq!(format!("{:?}", expr2), "(0xa + 0x14)");

        let expr3 = Expr::Mul(vec![Expr::Const(&a), Expr::Const(&b)]);
        assert_eq!(format!("{:?}", expr3), "(0xa * 0x14)");

        let expr4 = Expr::Neg(Box::new(Expr::Const(&a)));
        assert_eq!(format!("{:?}", expr4), "-0xa");

        let expr5 = Expr::Pow(Box::new(Expr::Const(&a)), 2);
        assert_eq!(format!("{:?}", expr5), "(0xa)^2");
    }
}
