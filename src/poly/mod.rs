use std::{
    collections::HashMap,
    fmt::Debug,
    hash::{DefaultHasher, Hash, Hasher},
    ops::{Add, Mul, Neg, Sub},
};

use halo2_proofs::plonk::Expression;

use crate::field::Field;

pub mod cse;
pub mod mielim;
pub mod reduce;
pub mod simplify;

pub trait ToExpr<F, V, M: Meta> {
    fn expr(&self) -> Expr<F, V, M>;
}

pub trait ToField<F> {
    fn field(&self) -> F;
}

pub trait Meta: Clone + Default + Debug + Hash {
    fn apply_meta<F: Field + Hash, V: Clone + Eq + Hash>(
        expr: &Expr<F, V, ()>,
        assignments: &VarAssignments<F, V>,
    ) -> Self;
}

#[derive(Clone)]
pub enum Expr<F, V, M: Meta> {
    Const(F, M),
    Sum(Vec<Expr<F, V, M>>, M),
    Mul(Vec<Expr<F, V, M>>, M),
    Neg(Box<Expr<F, V, M>>, M),
    Pow(Box<Expr<F, V, M>>, u32, M),
    Query(V, M),
    Halo2Expr(Expression<F>, M),
    MI(Box<Expr<F, V, M>>, M), //  Multiplicative inverse, but MI(0) = 0
}

impl Meta for () {
    fn apply_meta<F: Field + Hash, V: Clone + Eq + Hash>(
        _expr: &Expr<F, V, ()>,
        _assignments: &VarAssignments<F, V>,
    ) -> Self {
    }
}

impl Meta for HashResult {
    fn apply_meta<F: Field + Hash, V: Clone + Eq + Hash>(
        expr: &Expr<F, V, ()>,
        assignments: &VarAssignments<F, V>,
    ) -> Self {
        let hashed_expr = expr.hash(assignments);
        hashed_expr.meta().clone()
    }
}

#[derive(Debug, Clone, Default, Hash)]
pub struct HashResult {
    pub hash: u64,
    pub degree: usize,
}

impl HashResult {
    pub fn new<F: Field + Hash, V: Clone + Eq + Hash>(
        expr: &Expr<F, V, ()>,
        assignments: &VarAssignments<F, V>,
    ) -> Self {
        let mut hasher = DefaultHasher::new();

        // Custom hashing logic
        if let Some(result) = expr.eval(assignments) {
            result.hash(&mut hasher);
        }

        HashResult {
            hash: hasher.finish(),
            degree: expr.degree(),
        }
    }
}

impl<F: Clone, V: Clone, M: Meta> Expr<F, V, M> {
    pub fn degree(&self) -> usize {
        match self {
            Expr::Const(_, _) => 0,
            Expr::Sum(ses, _) => ses.iter().map(|se| se.degree()).max().unwrap_or(0),
            Expr::Mul(ses, _) => ses.iter().fold(0, |acc, se| acc + se.degree()),
            Expr::Neg(se, _) => se.degree(),
            Expr::Pow(se, exp, _) => se.degree() * (*exp as usize),
            Expr::Query(_, _) => 1,
            Expr::Halo2Expr(_, _) => panic!("not implemented"),
            Expr::MI(se, _) => se.degree(), /* Treat MI as not changing the degree of the inner
                                             * expression */
        }
    }

    pub fn meta(&self) -> &M {
        match self {
            Expr::Const(_, m) => m,
            Expr::Sum(_, m) => m,
            Expr::Mul(_, m) => m,
            Expr::Neg(_, m) => m,
            Expr::Pow(_, _, m) => m,
            Expr::Query(_, m) => m,
            Expr::Halo2Expr(_, m) => m,
            Expr::MI(_, m) => m,
        }
    }

    pub fn map_meta<N: Meta, Func: Fn(&M) -> N>(&self, f: Func) -> Expr<F, V, N> {
        match self {
            Expr::Const(v, m) => Expr::Const(v.clone(), f(m)),
            Expr::Sum(ses, m) => Expr::Sum(ses.iter().map(|e| e.map_meta(&f)).collect(), f(m)),
            Expr::Mul(ses, m) => Expr::Mul(ses.iter().map(|e| e.map_meta(&f)).collect(), f(m)),
            Expr::Neg(se, m) => Expr::Neg(Box::new(se.map_meta(&f)), f(m)),
            Expr::Pow(se, exp, m) => Expr::Pow(Box::new(se.map_meta(&f)), *exp, f(m)),
            Expr::Query(v, m) => Expr::Query(v.clone(), f(m)),
            Expr::Halo2Expr(e, m) => Expr::Halo2Expr(e.clone(), f(m)),
            Expr::MI(se, m) => Expr::MI(Box::new(se.map_meta(&f)), f(m)),
        }
    }
}

impl<F: Field + Hash, V: Debug + Clone + Eq + Hash, M: Meta> Expr<F, V, M> {
    pub fn with_meta<N: Meta>(&self, assignments: &VarAssignments<F, V>) -> Expr<F, V, N> {
        let expr_without_meta = self.without_meta();
        let new_meta = N::apply_meta(&expr_without_meta, assignments);
        match self {
            Expr::Const(v, _) => Expr::Const(*v, new_meta),
            Expr::Sum(ses, _) => Expr::Sum(
                ses.iter().map(|e| e.with_meta(assignments)).collect(),
                new_meta,
            ),
            Expr::Mul(ses, _) => Expr::Mul(
                ses.iter().map(|e| e.with_meta(assignments)).collect(),
                new_meta,
            ),
            Expr::Neg(se, _) => Expr::Neg(Box::new(se.with_meta(assignments)), new_meta),
            Expr::Pow(se, exp, _) => Expr::Pow(Box::new(se.with_meta(assignments)), *exp, new_meta),
            Expr::Query(v, _) => Expr::Query(v.clone(), new_meta),
            Expr::Halo2Expr(e, _) => Expr::Halo2Expr(e.clone(), new_meta),
            Expr::MI(se, _) => Expr::MI(Box::new(se.with_meta(assignments)), new_meta),
        }
    }

    pub fn apply_subexpressions<T>(&self, mut f: T) -> Self
    where
        T: FnMut(&Self) -> Self,
    {
        match self {
            Expr::Sum(ses, m) => Expr::Sum(ses.iter().map(&mut f).collect(), m.clone()),
            Expr::Mul(ses, m) => Expr::Mul(ses.iter().map(&mut f).collect(), m.clone()),
            Expr::Neg(se, m) => Expr::Neg(Box::new(f(se)), m.clone()),
            Expr::Pow(se, exp, m) => Expr::Pow(Box::new(f(se)), *exp, m.clone()),
            Expr::MI(se, m) => Expr::MI(Box::new(f(se)), m.clone()),
            _ => self.clone(),
        }
    }
}

impl<F: Field, V: Clone, M: Meta> Expr<F, V, M> {
    pub fn without_meta(&self) -> Expr<F, V, ()> {
        match self {
            Expr::Const(v, _) => Expr::Const(*v, ()),
            Expr::Query(v, _) => Expr::Query(v.clone(), ()),
            Expr::Sum(ses, _) => Expr::Sum(ses.iter().map(|e| e.without_meta()).collect(), ()),
            Expr::Mul(ses, _) => Expr::Mul(ses.iter().map(|e| e.without_meta()).collect(), ()),
            Expr::Neg(se, _) => Expr::Neg(Box::new(se.without_meta()), ()),
            Expr::Pow(se, exp, _) => Expr::Pow(Box::new(se.without_meta()), *exp, ()),
            Expr::Halo2Expr(e, _) => Expr::Halo2Expr(e.clone(), ()),
            Expr::MI(se, _) => Expr::MI(Box::new(se.without_meta()), ()),
        }
    }
}

impl<F: Field + Hash, V: Clone + Eq + Hash> Expr<F, V, ()> {
    pub fn hash(&self, assignments: &VarAssignments<F, V>) -> Expr<F, V, HashResult> {
        let hash_result = HashResult::new(self, assignments);

        match self {
            Expr::Const(v, _) => Expr::Const(*v, hash_result),
            Expr::Query(v, _) => Expr::Query(v.clone(), hash_result),
            Expr::Sum(ses, _) => {
                let new_ses = ses.iter().map(|se| se.hash(assignments)).collect();
                Expr::Sum(new_ses, hash_result)
            }
            Expr::Mul(ses, _) => {
                let new_ses = ses.iter().map(|se| se.hash(assignments)).collect();
                Expr::Mul(new_ses, hash_result)
            }
            Expr::Neg(se, _) => Expr::Neg(Box::new(se.hash(assignments)), hash_result),
            Expr::Pow(se, exp, _) => Expr::Pow(Box::new(se.hash(assignments)), *exp, hash_result),
            Expr::Halo2Expr(_, _) => panic!("not implemented"),
            Expr::MI(se, _) => Expr::MI(Box::new(se.hash(assignments)), hash_result),
        }
    }
}

impl<F: Debug, V: Debug, M: Meta> Debug for Expr<F, V, M> {
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

impl<F: Field + Hash, V: Eq + PartialEq + Hash, M: Meta> Expr<F, V, M> {
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

impl<F: Field + Hash, V: Eq + PartialEq + Hash + Clone, M: Meta> Expr<F, V, M> {
    /// Returns all the keys of the queries
    pub fn get_queries(&self) -> Vec<V> {
        match self {
            Expr::Const(_, _) => Vec::new(),
            Expr::Sum(ses, _) | Expr::Mul(ses, _) => {
                ses.iter().flat_map(|se| se.get_queries()).collect()
            }
            Expr::Neg(se, _) | Expr::Pow(se, _, _) | Expr::MI(se, _) => se.get_queries(),
            Expr::Query(q, _) => vec![q.clone()],
            Expr::Halo2Expr(_, _) => Vec::new(),
        }
    }
}

impl<F: Clone, V: Clone, M: Meta> ToExpr<F, V, M> for Expr<F, V, M> {
    fn expr(&self) -> Expr<F, V, M> {
        self.clone()
    }
}

/// TODO: M::default is a placeholder for now, the metadata should be updated
impl<F: Clone + From<u64>, V: Clone, M: Meta> Expr<F, V, M> {
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

impl<F, V, M: Meta, RHS: Into<Expr<F, V, M>>> Add<RHS> for Expr<F, V, M> {
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

impl<F, V, M: Meta, RHS: Into<Expr<F, V, M>>> Sub<RHS> for Expr<F, V, M> {
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

impl<F, V, M: Meta, RHS: Into<Expr<F, V, M>>> Mul<RHS> for Expr<F, V, M> {
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

impl<F, V, M: Meta> Neg for Expr<F, V, M> {
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
        impl<F: From<u64>, V, M: Meta> From<$type> for Expr<F, V, M> {
            #[inline]
            fn from(value: $type) -> Self {
                Expr::Const(F::from(value as u64), M::default())
            }
        }

        impl<F: From<u64>, V, M: Meta> $crate::poly::ToExpr<F, V, M> for $type {
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

impl<F: Field + From<u64>, V, M: Meta> From<i32> for Expr<F, V, M> {
    #[inline]
    fn from(value: i32) -> Self {
        Expr::Const(
            F::from(value.unsigned_abs() as u64)
                * if value.is_negative() { -F::ONE } else { F::ONE },
            M::default(),
        )
    }
}

impl<F: Field + From<u64>, V, M: Meta> ToExpr<F, V, M> for i32 {
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
pub struct ConstrDecomp<F, V, M: Meta> {
    /// PI constraint for the new signals introduced.
    pub constrs: Vec<Expr<F, V, M>>,
    /// Expressions for how to create the witness for the generated signals the orginal expression
    /// has be decomposed into.
    pub auto_signals: HashMap<V, Expr<F, V, M>>,
}

impl<F, V: Debug, M: Meta> ConstrDecomp<F, V, M> {
    pub fn get_auto_signal<S: Into<String> + Copy>(
        &self,
        annotation: S,
    ) -> Option<(&V, &Expr<F, V, M>)> {
        self.auto_signals.iter().find_map(|(s, e)| {
            if format!("{:#?}", s) == annotation.into() {
                Some((s, e))
            } else {
                None
            }
        })
    }
}

impl<F: Clone, V: Clone> ConstrDecomp<F, V, HashResult> {
    pub fn find_auto_signal_by_hash(&self, hash: u64) -> Option<(&V, &Expr<F, V, HashResult>)> {
        self.auto_signals.iter().find_map(|(s, e)| {
            if e.meta().hash == hash {
                Some((s, e))
            } else {
                None
            }
        })
    }
}

impl<F, V, M: Meta> Default for ConstrDecomp<F, V, M> {
    fn default() -> Self {
        Self {
            constrs: Default::default(),
            auto_signals: Default::default(),
        }
    }
}

impl<F: Clone, V: Clone + Eq + PartialEq + Hash, M: Meta> ConstrDecomp<F, V, M> {
    fn auto_eq(&mut self, signal: V, expr: Expr<F, V, M>) {
        self.constrs.push(Expr::Sum(
            vec![
                expr.clone(),
                Expr::Neg(
                    Box::new(Expr::Query(signal.clone(), M::default())),
                    M::default(),
                ),
            ],
            M::default(),
        ));

        self.auto_signals.insert(signal, expr);
    }
}

impl<F: Field, V: Clone + Hash + Eq> ConstrDecomp<F, V, HashResult> {
    pub fn without_meta(&self) -> ConstrDecomp<F, V, ()> {
        ConstrDecomp {
            constrs: self.constrs.iter().map(|c| c.without_meta()).collect(),
            auto_signals: self
                .auto_signals
                .iter()
                .map(|(k, v)| (k.clone(), v.without_meta()))
                .collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};
    use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

    use crate::{
        poly::{ToExpr, VarAssignments},
        sbpir::{query::Queriable, InternalSignal},
    };

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

        let expr: Expr<Fr, &str, ()> = (Query("a", ()) * Query("a", ()))
            + (Query("c", ()) * Query("d", ()))
            - Const(Fr::ONE, ());

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

    #[test]
    fn test_hash() {
        use super::Expr::*;

        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));
        let vars = vec![a, b, c, d, e, f, g];

        let mut assignments = VarAssignments::new();
        for v in &vars {
            assignments.insert(*v, Fr::random(&mut rng));
        }

        // Equivalent expressions
        let expr1 = Pow(Box::new(e.expr()), 6, ()) * a * b + c * d - 1.expr();
        let expr2 = d * c - 1.expr() + a * b * Pow(Box::new(e.expr()), 6, ());

        // Equivalent expressions
        let expr3 = f * b - c * d - 1.expr();
        let expr4 = -(1.expr()) - c * d + b * f;

        // Equivalent expressions
        let expr5 = -(-f * g) * (-(-(-a)));
        let expr6 = -(f * g * a);

        let expressions = [expr1, expr2, expr3, expr4, expr5, expr6];
        let mut hashed_expressions = Vec::new();

        for expr in expressions {
            let hashed_expr = expr.hash(&assignments);
            hashed_expressions.push(hashed_expr);
        }

        assert_eq!(
            hashed_expressions[0].meta().hash,
            hashed_expressions[1].meta().hash
        );

        assert_eq!(
            hashed_expressions[2].meta().hash,
            hashed_expressions[3].meta().hash
        );

        assert_eq!(
            hashed_expressions[4].meta().hash,
            hashed_expressions[5].meta().hash
        );

        assert_ne!(
            hashed_expressions[0].meta().hash,
            hashed_expressions[2].meta().hash
        );

        assert_ne!(
            hashed_expressions[0].meta().hash,
            hashed_expressions[4].meta().hash
        );

        assert_ne!(
            hashed_expressions[2].meta().hash,
            hashed_expressions[5].meta().hash
        );
    }

    #[test]
    fn test_get_queries() {
        use super::Expr::*;

        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));

        let expr = Pow(Box::new(e.expr()), 6, ()) * a * b + c * d - 1.expr();

        let queries = expr.get_queries();

        assert_eq!(queries.len(), 5);
        assert!(queries.contains(&a));
        assert!(queries.contains(&b));
        assert!(queries.contains(&c));
        assert!(queries.contains(&d));
        assert!(queries.contains(&e));
        assert!(!queries.contains(&f));
        assert!(!queries.contains(&g));
    }
}
