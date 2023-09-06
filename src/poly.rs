use std::{
    fmt::Debug,
    ops::{Add, Mul, Neg, Sub},
};

use halo2_proofs::plonk::Expression;

use crate::field::Field;

pub trait ToExpr<F, V> {
    fn expr(&self) -> Expr<F, V>;
}

pub trait ToField<F> {
    fn field(&self) -> F;
}

#[derive(Clone)]
pub enum Expr<F, V> {
    Const(F),
    Sum(Vec<Expr<F, V>>),
    Mul(Vec<Expr<F, V>>),
    Neg(Box<Expr<F, V>>),
    Pow(Box<Expr<F, V>>, u32),
    Query(V),
    Halo2Expr(Expression<F>),
}

impl<F: Debug, V: Debug> Debug for Expr<F, V> {
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
            Self::Neg(arg0) => write!(f, "(-{:?})", arg0),
            Self::Pow(arg0, arg1) => write!(f, "({:?})^{}", arg0, arg1),
            Self::Query(arg0) => write!(f, "{:?}", arg0),
            Self::Halo2Expr(arg0) => write!(f, "halo2({:?})", arg0),
        }
    }
}

impl<F: Clone, V: Clone> ToExpr<F, V> for Expr<F, V> {
    fn expr(&self) -> Expr<F, V> {
        self.clone()
    }
}

impl<F, V, RHS: Into<Expr<F, V>>> Add<RHS> for Expr<F, V> {
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

impl<F, V, RHS: Into<Expr<F, V>>> Sub<RHS> for Expr<F, V> {
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

impl<F, V, RHS: Into<Expr<F, V>>> Mul<RHS> for Expr<F, V> {
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

impl<F, V> Neg for Expr<F, V> {
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
        impl<F: From<u64>, V> From<$type> for Expr<F, V> {
            #[inline]
            fn from(value: $type) -> Self {
                Expr::Const(F::from(value as u64))
            }
        }

        impl<F: From<u64>, V> $crate::poly::ToExpr<F, V> for $type {
            #[inline]
            fn expr(&self) -> Expr<F, V> {
                Expr::Const(F::from(*self as u64))
            }
        }

        impl<F: From<u64>> $crate::poly::ToField<F> for $type {
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

impl<F: Field + From<u64>, V> From<i32> for Expr<F, V> {
    #[inline]
    fn from(value: i32) -> Self {
        Expr::Const(
            F::from(value.unsigned_abs() as u64)
                * if value.is_negative() { -F::ONE } else { F::ONE },
        )
    }
}

impl<F: Field + From<u64>, V> ToExpr<F, V> for i32 {
    #[inline]
    fn expr(&self) -> Expr<F, V> {
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

impl<F, V> From<Expression<F>> for Expr<F, V> {
    #[inline]
    fn from(value: Expression<F>) -> Self {
        Expr::Halo2Expr(value)
    }
}
