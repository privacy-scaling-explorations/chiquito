use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

use halo2_proofs::{arithmetic::Field, plonk::Expression};

use crate::dsl::cb::Constraint;

use self::query::Queriable;

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
            Self::Const(arg0) => write!(f, "{:?}", arg0),
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
                * if value.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

impl<F: Field + From<u64>> ToExpr<F> for i32 {
    #[inline]
    fn expr(&self) -> Expr<F> {
        Expr::Const(
            F::from(self.unsigned_abs() as u64)
                * if self.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

impl<F: Field + From<u64>> ToField<F> for i32 {
    #[inline]
    fn field(&self) -> F {
        F::from(self.unsigned_abs() as u64)
            * if self.is_negative() {
                -F::one()
            } else {
                F::one()
            }
    }
}

impl<F> From<Expression<F>> for Expr<F> {
    #[inline]
    fn from(value: Expression<F>) -> Self {
        Expr::Halo2Expr(value)
    }
}

pub mod query {
    use std::{
        fmt::Debug,
        marker::PhantomData,
        ops::{Add, Mul, Neg, Sub},
    };

    use crate::{
        ast::{ForwardSignal, ImportedHalo2Advice, ImportedHalo2Fixed, InternalSignal},
        dsl::StepTypeHandler,
    };

    use super::{Expr, ToExpr};

    // Queriable
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum Queriable<F> {
        Internal(InternalSignal),
        Forward(ForwardSignal, bool),
        StepTypeNext(StepTypeHandler),
        Halo2AdviceQuery(ImportedHalo2Advice, i32),
        Halo2FixedQuery(ImportedHalo2Fixed, i32),
        #[allow(non_camel_case_types)]
        _unaccessible(PhantomData<F>),
    }

    impl<F> Debug for Queriable<F> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.annotation())
        }
    }

    impl<F> Queriable<F> {
        /// # **Description:**
        /// Call `**next**` function on a `**Querible**` forward signal to build constraints for forward signal with rotation. Cannot be called on an internal signal and must be used within a `**transition**` constraint.
        /// # **Return:**
        /// A new **`Queriable`** forward signal with rotation.
        pub fn next(&self) -> Queriable<F> {
            use Queriable::*;
            match self {
                Forward(s, rot) => {
                    if !*rot {
                        Forward(*s, true)
                    } else {
                        panic!("jarrl: cannot rotate next(forward)")
                    }
                }
                Halo2AdviceQuery(s, rot) => Halo2AdviceQuery(*s, rot + 1),
                Halo2FixedQuery(s, r) => Halo2FixedQuery(*s, r + 1),
                _ => panic!("can only next a forward or halo2 column"),
            }
        }

        pub fn uuid(&self) -> u32 {
            match self {
                Queriable::Internal(s) => s.uuid(),
                Queriable::Forward(s, _) => s.uuid(),
                Queriable::StepTypeNext(s) => s.uuid(),
                Queriable::Halo2AdviceQuery(s, _) => s.uuid(),
                Queriable::Halo2FixedQuery(s, _) => s.uuid(),
                Queriable::_unaccessible(_) => panic!("jarrl wrong queriable type"),
            }
        }

        pub fn annotation(&self) -> String {
            match self {
                Queriable::Internal(s) => s.annotation.to_string(),
                Queriable::Forward(s, rot) => {
                    if !rot {
                        s.annotation.to_string()
                    } else {
                        format!("next({})", s.annotation)
                    }
                }
                Queriable::StepTypeNext(s) => s.annotation.to_string(),
                Queriable::Halo2AdviceQuery(s, rot) => {
                    if *rot != 0 {
                        format!("{}(rot {})", s.annotation, rot)
                    } else {
                        s.annotation.to_string()
                    }
                }
                Queriable::Halo2FixedQuery(s, rot) => {
                    if *rot != 0 {
                        format!("{}(rot {})", s.annotation, rot)
                    } else {
                        s.annotation.to_string()
                    }
                }
                Queriable::_unaccessible(_) => todo!(),
            }
        }
    }

    impl<F: Clone> ToExpr<F> for Queriable<F> {
        fn expr(&self) -> Expr<F> {
            Expr::Query((*self).clone())
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Add<RHS> for Queriable<F> {
        type Output = Expr<F>;

        fn add(self, rhs: RHS) -> Self::Output {
            self.expr() + rhs
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Sub<RHS> for Queriable<F> {
        type Output = Expr<F>;

        fn sub(self, rhs: RHS) -> Self::Output {
            self.expr() - rhs
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Mul<RHS> for Queriable<F> {
        type Output = Expr<F>;

        fn mul(self, rhs: RHS) -> Self::Output {
            self.expr() * rhs
        }
    }

    impl<F: Clone> Neg for Queriable<F> {
        type Output = Expr<F>;

        fn neg(self) -> Self::Output {
            self.expr().neg()
        }
    }
}
