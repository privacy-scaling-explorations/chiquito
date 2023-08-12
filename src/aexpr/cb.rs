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
