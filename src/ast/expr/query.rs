use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
};

use crate::{
    ast::{
        FixedSignal, ForwardSignal, ImportedHalo2Advice, ImportedHalo2Fixed, InternalSignal,
        SharedSignal,
    },
    frontend::dsl::StepTypeHandler,
    util::UUID,
};

use super::{Expr, ToExpr};

// Queriable
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Queriable<F> {
    Internal(InternalSignal),
    Forward(ForwardSignal, bool),
    Shared(SharedSignal, i32),
    Fixed(FixedSignal, i32),
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
    /// Call `next` function on a `Querible` forward signal to build constraints for forward
    /// signal with rotation. Cannot be called on an internal signal and must be used within a
    /// `transition` constraint. Returns a new `Queriable` forward signal with rotation.
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
            Shared(s, rot) => Shared(*s, rot + 1),
            Fixed(s, rot) => Fixed(*s, rot + 1),
            Halo2AdviceQuery(s, rot) => Halo2AdviceQuery(*s, rot + 1),
            Halo2FixedQuery(s, r) => Halo2FixedQuery(*s, r + 1),
            _ => panic!("can only next a forward, shared, fixed, or halo2 column"),
        }
    }

    /// Call `prev` function on a `Querible` shared signal to build constraints for shared
    /// signal that decreases rotation by 1. Must be called on a shared signal and used within a
    /// `transition` constraint. Returns a new `Queriable` shared signal with positive or
    /// negative rotation.
    pub fn prev(&self) -> Queriable<F> {
        use Queriable::*;
        match self {
            Shared(s, rot) => Shared(*s, rot - 1),
            Fixed(s, rot) => Fixed(*s, rot - 1),
            _ => panic!("can only prev a shared or fixed column"),
        }
    }

    /// Call `rot` function on a `Querible` shared signal to build constraints for shared signal
    /// with arbitrary rotation. Must be called on a shared signal and used within a
    /// `transition` constraint. Returns a new `Queriable` shared signal with positive or
    /// negative rotation.
    pub fn rot(&self, rotation: i32) -> Queriable<F> {
        use Queriable::*;
        match self {
            Shared(s, rot) => Shared(*s, rot + rotation),
            Fixed(s, rot) => Fixed(*s, rot + rotation),
            _ => panic!("can only rot a shared or fixed column"),
        }
    }

    pub fn uuid(&self) -> UUID {
        match self {
            Queriable::Internal(s) => s.uuid(),
            Queriable::Forward(s, _) => s.uuid(),
            Queriable::Shared(s, _) => s.uuid(),
            Queriable::Fixed(s, _) => s.uuid(),
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
            Queriable::Shared(s, rot) => {
                if *rot != 0 {
                    format!("{}(rot {})", s.annotation, rot)
                } else {
                    s.annotation.to_string()
                }
            }
            Queriable::Fixed(s, rot) => {
                if *rot != 0 {
                    format!("{}(rot {})", s.annotation, rot)
                } else {
                    s.annotation.to_string()
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
