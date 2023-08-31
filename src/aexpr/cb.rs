use super::AExpr;

pub fn eq<F, V, LHS: Into<AExpr<F, V>>, RHS: Into<AExpr<F, V>>>(lhs: LHS, rhs: RHS) -> AExpr<F, V> {
    AExpr::Eq(Box::new(lhs.into()), Box::new(rhs.into()))
}

pub fn neq<F, V, LHS: Into<AExpr<F, V>>, RHS: Into<AExpr<F, V>>>(
    lhs: LHS,
    rhs: RHS,
) -> AExpr<F, V> {
    AExpr::NEq(Box::new(lhs.into()), Box::new(rhs.into()))
}

pub fn and<F, V, E: Into<AExpr<F, V>>, I: IntoIterator<Item = E>>(input: I) -> AExpr<F, V> {
    let sub_exprs: Vec<AExpr<F, V>> = input.into_iter().map(|e| e.into()).collect();

    AExpr::And(sub_exprs)
}

pub fn or<F, V, E: Into<AExpr<F, V>>, I: IntoIterator<Item = E>>(input: I) -> AExpr<F, V> {
    let sub_exprs: Vec<AExpr<F, V>> = input.into_iter().map(|e| e.into()).collect();

    AExpr::Or(sub_exprs)
}

pub fn not<F, V, E: Into<AExpr<F, V>>>(expr: E) -> AExpr<F, V> {
    AExpr::Not(Box::new(expr.into()))
}

pub fn ifthen<F, V, SEL: Into<AExpr<F, V>>, THEN: Into<AExpr<F, V>>>(
    selector: SEL,
    then: THEN,
) -> AExpr<F, V> {
    AExpr::IfThen(Box::new(selector.into()), Box::new(then.into()))
}

pub fn ifthenelse<
    F,
    V,
    SEL: Into<AExpr<F, V>>,
    THEN: Into<AExpr<F, V>>,
    ELSE: Into<AExpr<F, V>>,
>(
    selector: SEL,
    then: THEN,
    elsex: ELSE,
) -> AExpr<F, V> {
    AExpr::IfThenElse(
        Box::new(selector.into()),
        Box::new(then.into()),
        Box::new(elsex.into()),
    )
}

pub fn select<F, V, SEL: Into<AExpr<F, V>>, WHENT: Into<AExpr<F, V>>, WHENF: Into<AExpr<F, V>>>(
    selector: SEL,
    when_true: WHENT,
    when_false: WHENF,
) -> AExpr<F, V> {
    AExpr::Select(
        Box::new(selector.into()),
        Box::new(when_true.into()),
        Box::new(when_false.into()),
    )
}

pub trait ToAExpr<F, V> {
    fn to_aexpr(self) -> AExpr<F, V>;
}

macro_rules! aexpr_build {
    (($lhs:tt == $rhs:tt)) => {
        eq(aexpr_build!($lhs), aexpr_build!($rhs))
    };

    ($lhs:tt == $rhs:tt) => {
        eq(aexpr_build!($lhs), aexpr_build!($rhs))
    };

    (($lhs:tt != $rhs:tt)) => {
        neq(aexpr_build!($lhs), aexpr_build!($rhs))
    };

    ($lhs:tt != $rhs:tt) => {
        neq(aexpr_build!($lhs), aexpr_build!($rhs))
    };

    (( $first_operand:tt $(and $operands:tt )+)) => {
        and(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ($first_operand:tt $(and $operands:tt )+) => {
        and(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    (( $first_operand:tt $(or $operands:tt )+)) => {
        AExpr::Or(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ($first_operand:tt $(or $operands:tt )+) => {
        AExpr::Or(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ((not $operand:tt)) => {
        not(aexpr_build!($operand))
    };

    (not $operand:tt) => {
        not(aexpr_build!($operand))
    };

    (ifx $selector:tt thenx { $then:tt }) => {
        ifthen(aexpr_build!($selector), aexpr_build!($then))
    };

    ((ifx $selector:tt thenx $then:tt)) => {
        ifthen(aexpr_build!($selector), aexpr_build!($then))
    };

    (ifx $selector:tt thenx $then:tt) => {
        ifthen(aexpr_build!($selector), aexpr_build!($then))
    };

    (( $first_operand:tt $(+ $operands:tt )+)) => {
        AExpr::Sum(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ($first_operand:tt $(+ $operands:tt )+) => {
        AExpr::Sum(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    (( $first_operand:tt $(* $operands:tt )+)) => {
        AExpr::Sum(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ($first_operand:tt $(* $operands:tt )+) => {
        AExpr::Mul(vec![aexpr_build!($first_operand), $(aexpr_build!($operands)),+])
    };

    ((- $operand:tt)) => {
        AExpr::Neg(Box::new(aexpr_build!($operand)))
    };

    (- $operand:tt) => {
        AExpr::Neg(aexpr_build!($operand))
    };

    ($e:expr) => {
        $e.to_aexpr()
    }
}

#[cfg(test)]
mod test {
    use halo2curves::{bn256::Fr, ff::Field};

    use crate::{aexpr::{compiler::compile, ir::CostConfig, poly}, ast::{InternalSignal, query::Queriable, ToField}};

    use super::{super::AExpr, *};

    #[derive(Debug, Clone, Default, Copy)]
    struct TestSignal {}

    impl<F> super::ToAExpr<F, TestSignal> for TestSignal {
        fn to_aexpr(self) -> AExpr<F, TestSignal> {
            AExpr::Query(self)
        }
    }

    impl<F> super::ToAExpr<F, Queriable<F>> for Queriable<F> {
        fn to_aexpr(self) -> AExpr<F, Queriable<F>> {
            AExpr::Query(self)
        }
    }

    impl<F: Field + From<u64>, V> ToAExpr<F, V> for i32 {
        fn to_aexpr(self) -> AExpr<F, V> {
            AExpr::Const(F::from(self.unsigned_abs() as u64) * if self.is_negative() { -F::ONE } else { F::ONE },)
        }
    }

    impl<F: Field + From<u64>, V> From<i32> for AExpr<F, V> {
        fn from(value: i32) -> Self {
            AExpr::Const(
                F::from(value.unsigned_abs() as u64)
            * if value.is_negative() { -F::ONE } else { F::ONE },
        )
        }
    }

    #[test]
    fn test_macro() {
        //trace_macros!(true);
        let a = Queriable::Internal(InternalSignal::new("a".to_string()));
        
        let constr = aexpr_build!(2i32 + a);

        println!("{:#?}", constr);

        let constr = aexpr_build!((2i32 + a) == 3i32);

        println!("{:#?}", constr);

        let constr = aexpr_build!(((1 + 2 + -a + 10) == 3i32) and a);
        println!("{:#?}", constr);

        let constr: AExpr<Fr, Queriable<Fr>> = aexpr_build!(ifx (not a) thenx { (((2 + a + 10) == 3i32) and a ) } );
        println!("{:#?}", constr);

        let compiled = poly::compile(&compile(&constr, CostConfig::default()));

        println!("{:#?}", compiled);
    }
}
