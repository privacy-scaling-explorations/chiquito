use std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    ops::{Add, Mul, Neg, Sub},
};

use halo2_proofs::plonk::Expression;

use crate::field::Field;

pub mod mielim;
pub mod reduce;
pub mod simplify;

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

    MI(Box<Expr<F, V>>),
}

impl<F, V> Expr<F, V> {
    pub fn degree(&self) -> usize {
        match self {
            Expr::Const(_) => 0,
            Expr::Sum(ses) => ses.iter().map(|se| se.degree()).max().unwrap(),
            Expr::Mul(ses) => ses.iter().fold(0, |acc, se| acc + se.degree()),
            Expr::Neg(se) => se.degree(),
            Expr::Pow(se, exp) => se.degree() * (*exp as usize),
            Expr::Query(_) => 1,
            Expr::Halo2Expr(_) => panic!("not implemented"),
            Expr::MI(_) => panic!("not implemented"),
        }
    }
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
            Self::MI(arg0) => write!(f, "mi({:?})", arg0),
        }
    }
}

pub type VarAssignments<F, V> = HashMap<V, F>;

impl<F: Field + Hash, V: Eq + PartialEq + Hash> Expr<F, V> {
    pub fn eval(&self, assignments: &VarAssignments<F, V>) -> Option<F> {
        match self {
            Expr::Const(v) => Some(*v),
            Expr::Sum(ses) => ses
                .iter()
                .try_fold(F::ZERO, |acc, se| Some(acc + se.eval(assignments)?)),
            Expr::Mul(ses) => ses
                .iter()
                .try_fold(F::ONE, |acc, se| Some(acc * se.eval(assignments)?)),
            Expr::Neg(se) => Some(F::ZERO - se.eval(assignments)?),
            Expr::Pow(se, exp) => Some(se.eval(assignments)?.pow([*exp as u64])),
            Expr::Query(q) => assignments.get(q).copied(),
            Expr::MI(se) => Some(se.eval(assignments)?.mi()),

            // Not implemented, and not necessary for aexpr
            Expr::Halo2Expr(_) => None,
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

pub trait SignalFactory<V> {
    fn create<S: Into<String>>(&mut self, annotation: S) -> V;
}

/// The result of decomposing a PI into several
#[derive(Debug, Clone)]
pub struct ConstrDecomp<F, V> {
    /// PI constraint for the new signals introduced.
    constrs: Vec<Expr<F, V>>,
    /// Expressions for how to create the witness for the generated signals the original expression
    /// has be decomposed into.
    auto_signals: HashMap<V, Expr<F, V>>,
}

impl<F, V> Default for ConstrDecomp<F, V> {
    fn default() -> Self {
        Self {
            constrs: Default::default(),
            auto_signals: Default::default(),
        }
    }
}

impl<F: Clone, V: Clone + Eq + PartialEq + Hash> ConstrDecomp<F, V> {
    fn auto_eq(&mut self, signal: V, expr: Expr<F, V>) {
        self.constrs.push(Expr::Sum(vec![
            expr.clone(),
            Expr::Neg(Box::new(Expr::Query(signal.clone()))),
        ]));

        self.auto_signals.insert(signal, expr);
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{field::Field, poly::VarAssignments};

    use super::Expr;

    #[test]
    fn eval_const() {
        use super::Expr::*;

        let experiment: Expr<Fr, String> = Const(Fr::ONE);
        let assignments: VarAssignments<Fr, String> = VarAssignments::default();

        assert_eq!(experiment.eval(&assignments), Some(Fr::ONE))
    }

    #[test]
    fn eval_var() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str> = Query("a");
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::ONE);

        assert_eq!(experiment.eval(&assignments), Some(Fr::ONE))
    }

    #[test]
    fn eval_expr() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str> = (Query("a") * Query("b")) + Query("c") - Const(Fr::ONE);
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::from(2));
        assignments.insert("b", Fr::from(3));
        assignments.insert("c", Fr::from(4));

        assert_eq!(experiment.eval(&assignments), Some(Fr::from(9)))
    }

    #[test]
    fn eval_expr_missing_var() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str> = (Query("a") * Query("b")) + Query("c") - Const(Fr::ONE);
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::from(2));
        // REMOVE assignments.insert("b", Fr::from(3));
        assignments.insert("c", Fr::from(4));

        assert_eq!(experiment.eval(&assignments), None)
    }

    #[test]
    fn test_degree_expr() {
        use super::Expr::*;

        let expr: Expr<Fr, &str> =
            (Query("a") * Query("a")) + (Query("c") * Query("d")) - Const(Fr::ONE);

        assert_eq!(expr.degree(), 2);

        let expr: Expr<Fr, &str> =
            (Query("a") * Query("a")) + (Query("c") * Query("d")) * Query("e");

        assert_eq!(expr.degree(), 3);
    }

    #[test]
    fn test_expr_sum() {
        use super::Expr::*;

        let lhs: Expr<Fr, &str> = Query("a") + Query("b");

        let rhs: Expr<Fr, &str> = Query("c") + Query("d");

        assert_eq!(
            format!("({:?} + {:?})", lhs, rhs),
            format!("{:?}", Sum(vec![lhs, rhs]))
        );
    }

    #[test]
    fn test_expr_mul() {
        use super::Expr::*;

        let lhs: Expr<Fr, &str> = Query("a") * Query("b");

        let rhs: Expr<Fr, &str> = Query("c") * Query("d");

        assert_eq!(
            format!("({:?} * {:?})", lhs, rhs),
            format!("{:?}", Mul(vec![lhs, rhs]))
        );
    }

    #[test]
    fn test_expr_neg() {
        use super::Expr::*;

        let expr: Expr<Fr, &str> = Query("a") + Query("b");

        assert_eq!(
            format!("(-{:?})", expr),
            format!("{:?}", Neg(Box::new(expr)))
        );

        let lhs: Expr<Fr, &str> = Query("a") * Query("b");
        let rhs: Expr<Fr, &str> = Query("c") + Query("d");

        let expr: Expr<Fr, &str> = lhs.clone() - rhs.clone();

        assert_eq!(
            format!("{:?}", Sum(vec![lhs, Neg(Box::new(rhs))])),
            format!("{:?}", expr)
        );
    }
}
