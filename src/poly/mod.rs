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

pub trait ToExpr<F, V, M> {
    fn expr(&self) -> Expr<F, V, M>;
}

pub trait ToField<F> {
    fn field(&self) -> F;
}

#[derive(Clone)]
pub enum Expr<F, V, M> {
    Const(F, M),
    Sum(Vec<Expr<F, V, M>>, M),
    Mul(Vec<Expr<F, V, M>>, M),
    Neg(Box<Expr<F, V, M>>, M),
    Pow(Box<Expr<F, V, M>>, u32, M),
    Query(V, M),
    Halo2Expr(Expression<F>, M),

    MI(Box<Expr<F, V, M>>, M), //  Multiplicative inverse, but MI(0) = 0
}

impl<F, V, M> Expr<F, V, M> {
    pub fn degree(&self) -> usize {
        match self {
            Expr::Const(_, _) => 0,
            Expr::Sum(ses, _) => ses.iter().map(|se| se.degree()).max().unwrap(),
            Expr::Mul(ses, _) => ses.iter().fold(0, |acc, se| acc + se.degree()),
            Expr::Neg(se, _) => se.degree(),
            Expr::Pow(se, exp, _) => se.degree() * (*exp as usize),
            Expr::Query(_, _) => 1,
            Expr::Halo2Expr(_, _) => panic!("not implemented"),
            Expr::MI(_, _) => panic!("not implemented"),
        }
    }
}

impl<F: Debug, V: Debug, M: Debug> Debug for Expr<F, V, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(arg0, _) => {
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
            Self::Sum(arg0, _) => write!(
                f,
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" + ")
            ),
            Self::Mul(arg0, _) => write!(
                f,
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" * ")
            ),
            Self::Neg(arg0, _) => write!(f, "(-{:?})", arg0),
            Self::Pow(arg0, arg1, _) => write!(f, "({:?})^{}", arg0, arg1),
            Self::Query(arg0, _) => write!(f, "{:?}", arg0),
            Self::Halo2Expr(arg0, _) => write!(f, "halo2({:?})", arg0),
            Self::MI(arg0, _) => write!(f, "mi({:?})", arg0),
        }
    }
}

pub type VarAssignments<F, V> = HashMap<V, F>;

impl<F: Field + Hash, V: Eq + PartialEq + Hash, M: Eq + PartialEq + Hash> Expr<F, V, M> {
    pub fn eval(&self, assignments: &VarAssignments<F, V>) -> Option<F> {
        match self {
            Expr::Const(v, _) => Some(*v),
            Expr::Sum(ses, _) => ses
                .iter()
                .try_fold(F::ZERO, |acc, se| Some(acc + se.eval(assignments)?)),
            Expr::Mul(ses, _) => ses
                .iter()
                .try_fold(F::ONE, |acc, se| Some(acc * se.eval(assignments)?)),
            Expr::Neg(se, _) => Some(F::ZERO - se.eval(assignments)?),
            Expr::Pow(se, exp, _) => Some(se.eval(assignments)?.pow([*exp as u64])),
            Expr::Query(q, _) => assignments.get(q).copied(),
            Expr::MI(se, _) => Some(se.eval(assignments)?.mi()),

            // Not implemented, and not necessary for aexpr
            Expr::Halo2Expr(_, _) => None,
        }
    }
}

impl<F: Clone, V: Clone, M: Clone> ToExpr<F, V, M> for Expr<F, V, M> {
    fn expr(&self) -> Expr<F, V, M> {
        self.clone()
    }
}

/// TODO: M::default is a placeholder for now, the metadata should be updated
impl<F: Clone + From<u64>, V: Clone, M: Clone + Default> Expr<F, V, M> {
    /// Returns (1-self).
    pub fn one_minus(&self) -> Self {
        use Expr::Const;

        Const(F::from(1u64), M::default()) + (-self.clone())
    }

    /// Casts OneZero representation to anti-booly representation.
    pub fn cast_anti_booly(&self) -> Self {
        self.one_minus()
    }

    /// Casts anti-booly represation to OneZero representation.
    pub fn cast_one_zero(&self) -> Self {
        use Expr::MI;

        (self.clone() * MI(Box::new(self.clone()), M::default())).one_minus()
    }
}

impl<F, V, M: Default, RHS: Into<Expr<F, V, M>>> Add<RHS> for Expr<F, V, M> {
    type Output = Self;
    fn add(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs, _) => {
                xs.push(rhs.into());
                Sum(xs, M::default())
            }
            e => Sum(vec![e, rhs.into()], M::default()),
        }
    }
}

impl<F, V, M: Default, RHS: Into<Expr<F, V, M>>> Sub<RHS> for Expr<F, V, M> {
    type Output = Self;
    fn sub(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs, _) => {
                xs.push(rhs.into().neg());
                Sum(xs, M::default())
            }
            e => Sum(vec![e, rhs.into().neg()], M::default()),
        }
    }
}

impl<F, V, M: Default, RHS: Into<Expr<F, V, M>>> Mul<RHS> for Expr<F, V, M> {
    type Output = Self;
    fn mul(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Mul(mut xs, _) => {
                xs.push(rhs.into());
                Mul(xs, M::default())
            }
            e => Mul(vec![e, rhs.into()], M::default()),
        }
    }
}

impl<F, V, M: Default> Neg for Expr<F, V, M> {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Expr::Neg(xs, _) => *xs,
            e => Expr::Neg(Box::new(e), M::default()),
        }
    }
}

macro_rules! impl_expr_like {
    ($type:ty) => {
        impl<F: From<u64>, V, M: Default> From<$type> for Expr<F, V, M> {
            #[inline]
            fn from(value: $type) -> Self {
                Expr::Const(F::from(value as u64), M::default())
            }
        }

        impl<F: From<u64>, V, M: Default> $crate::poly::ToExpr<F, V, M> for $type {
            #[inline]
            fn expr(&self) -> Expr<F, V, M> {
                Expr::Const(F::from(*self as u64), M::default())
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

impl<F: Field + From<u64>, V, M: Default> From<i32> for Expr<F, V, M> {
    #[inline]
    fn from(value: i32) -> Self {
        Expr::Const(
            F::from(value.unsigned_abs() as u64)
                * if value.is_negative() { -F::ONE } else { F::ONE },
            M::default(),
        )
    }
}

impl<F: Field + From<u64>, V, M: Default> ToExpr<F, V, M> for i32 {
    #[inline]
    fn expr(&self) -> Expr<F, V, M> {
        Expr::Const(
            F::from(self.unsigned_abs() as u64) * if self.is_negative() { -F::ONE } else { F::ONE },
            M::default(),
        )
    }
}

impl<F: Field + From<u64>> ToField<F> for i32 {
    #[inline]
    fn field(&self) -> F {
        F::from(self.unsigned_abs() as u64) * if self.is_negative() { -F::ONE } else { F::ONE }
    }
}

impl<F, V> From<Expression<F>> for Expr<F, V, ()> {
    #[inline]
    fn from(value: Expression<F>) -> Self {
        Expr::Halo2Expr(value, ())
    }
}

pub trait SignalFactory<V> {
    fn create<S: Into<String>>(&mut self, annotation: S) -> V;
}

/// The result of decomposing a PI into several
#[derive(Debug, Clone)]
pub struct ConstrDecomp<F, V> {
    /// PI constraint for the new signals introduced.
    pub constrs: Vec<Expr<F, V, ()>>,
    /// Expressions for how to create the witness for the generated signals the orginal expression
    /// has be decomposed into.
    pub auto_signals: HashMap<V, Expr<F, V, ()>>,
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
    fn auto_eq(&mut self, signal: V, expr: Expr<F, V, ()>) {
        self.constrs.push(Expr::Sum(
            vec![
                expr.clone(),
                Expr::Neg(Box::new(Expr::Query(signal.clone(), ())), ()),
            ],
            (),
        ));

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

        let experiment: Expr<Fr, String, ()> = Const(Fr::ONE, ());
        let assignments: VarAssignments<Fr, String> = VarAssignments::default();

        assert_eq!(experiment.eval(&assignments), Some(Fr::ONE))
    }

    #[test]
    fn eval_var() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str, ()> = Query("a", ());
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::ONE);

        assert_eq!(experiment.eval(&assignments), Some(Fr::ONE))
    }

    #[test]
    fn eval_expr() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str, ()> =
            (Query("a", ()) * Query("b", ())) + Query("c", ()) - Const(Fr::ONE, ());
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::from(2));
        assignments.insert("b", Fr::from(3));
        assignments.insert("c", Fr::from(4));

        assert_eq!(experiment.eval(&assignments), Some(Fr::from(9)))
    }

    #[test]
    fn eval_expr_missing_var() {
        use super::Expr::*;

        let experiment: Expr<Fr, &str, ()> =
            (Query("a", ()) * Query("b", ())) + Query("c", ()) - Const(Fr::ONE, ());
        let mut assignments: VarAssignments<Fr, &str> = VarAssignments::default();
        assignments.insert("a", Fr::from(2));
        // REMOVE assignments.insert("b", Fr::from(3));
        assignments.insert("c", Fr::from(4));

        assert_eq!(experiment.eval(&assignments), None)
    }

    #[test]
    fn test_degree_expr() {
        use super::Expr::*;

        let expr: Expr<Fr, &str, ()> =
            (Query("a", ()) * Query("a", ())) + (Query("c", ()) * Query("d", ())) - Const(Fr::ONE, ());

        assert_eq!(expr.degree(), 2);

        let expr: Expr<Fr, &str, ()> =
            (Query("a", ()) * Query("a", ())) + (Query("c", ()) * Query("d", ())) * Query("e", ());

        assert_eq!(expr.degree(), 3);
    }

    #[test]
    fn test_expr_sum() {
        use super::Expr::*;

        let lhs: Expr<Fr, &str, ()> = Query("a", ()) + Query("b", ());

        let rhs: Expr<Fr, &str, ()> = Query("c", ()) + Query("d", ());

        assert_eq!(
            format!("({:?} + {:?})", lhs, rhs),
            format!("{:?}", Sum(vec![lhs, rhs], ()))
        );
    }

    #[test]
    fn test_expr_mul() {
        use super::Expr::*;

        let lhs: Expr<Fr, &str, ()> = Query("a", ()) * Query("b", ());

        let rhs: Expr<Fr, &str, ()> = Query("c", ()) * Query("d", ());

        assert_eq!(
            format!("({:?} * {:?})", lhs, rhs),
            format!("{:?}", Mul(vec![lhs, rhs], ()))
        );
    }

    #[test]
    fn test_expr_neg() {
        use super::Expr::*;

        let expr: Expr<Fr, &str, ()> = Query("a", ()) + Query("b", ());

        assert_eq!(
            format!("(-{:?})", expr),
            format!("{:?}", Neg(Box::new(expr), ()))
        );

        let lhs: Expr<Fr, &str, ()> = Query("a", ()) * Query("b", ());
        let rhs: Expr<Fr, &str, ()> = Query("c", ()) + Query("d", ());

        let expr: Expr<Fr, &str, ()> = lhs.clone() - rhs.clone();

        assert_eq!(
            format!("{:?}", Sum(vec![lhs, Neg(Box::new(rhs), ())], ())),
            format!("{:?}", expr)
        );
    }
}
