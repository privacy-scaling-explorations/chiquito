pub mod cb;
pub mod compiler;
pub mod ir;
pub mod poly;

#[derive(Debug,Clone)]
pub enum AExpr<F, V> {
    Const(F),
    Sum(Vec<AExpr<F, V>>),
    Mul(Vec<AExpr<F, V>>),
    Neg(Box<AExpr<F, V>>),
    Pow(Box<AExpr<F, V>>, u32),

    Eq(Box<AExpr<F, V>>, Box<AExpr<F, V>>),
    NEq(Box<AExpr<F, V>>, Box<AExpr<F, V>>),

    And(Vec<AExpr<F, V>>),
    Or(Vec<AExpr<F, V>>),
    Not(Box<AExpr<F, V>>),

    IfThen(Box<AExpr<F, V>>, Box<AExpr<F, V>>),
    IfThenElse(Box<AExpr<F, V>>, Box<AExpr<F, V>>, Box<AExpr<F, V>>),

    Select(Box<AExpr<F, V>>, Box<AExpr<F, V>>, Box<AExpr<F, V>>),

    Query(V),
}

impl<F, V> AExpr<F, V> {
    pub fn is_arith(&self) -> bool {
        match self {
            AExpr::Const(_) | AExpr::Sum(_) | AExpr::Mul(_) | AExpr::Neg(_) | AExpr::Pow(_, _) => {
                true
            }
            AExpr::Select(_, a, b) => a.is_arith() && b.is_arith(),
            _ => false,
        }
    }

    pub fn is_logic(&self) -> bool {
        match self {
            AExpr::Eq(_, _)
            | AExpr::NEq(_, _)
            | AExpr::And(_)
            | AExpr::Or(_)
            | AExpr::Not(_)
            | AExpr::IfThen(_, _)
            | AExpr::IfThenElse(_, _, _) => true,
            AExpr::Select(_, a, b) => a.is_logic() && b.is_logic(),
            _ => false,
        }
    }

    pub fn is_query(&self) -> bool {
        match self {
            AExpr::Query(_) => true,
            _ => false,
        }
    }
}

impl<F: Clone, V> AExpr<F, V> {
    pub fn var_change<OV, CB: Fn(&V) -> OV + Clone>(&self, callback: CB) -> AExpr<F, OV> {
        match self {
            AExpr::Const(v) => AExpr::Const(v.clone()),
            AExpr::Sum(vs) => AExpr::Sum(
                vs.into_iter()
                    .map(|e| e.var_change(callback.clone()))
                    .collect(),
            ),
            AExpr::Mul(vs) => AExpr::Mul(
                vs.into_iter()
                    .map(|e| e.var_change(callback.clone()))
                    .collect(),
            ),
            AExpr::Neg(v) => AExpr::Neg(Box::new(v.var_change(callback.clone()))),
            AExpr::Pow(v, e) => AExpr::Pow(Box::new(v.var_change(callback.clone())), *e),
            AExpr::Eq(lhs, rhs) => AExpr::Eq(
                Box::new(lhs.var_change(callback.clone())),
                Box::new(rhs.var_change(callback.clone())),
            ),
            AExpr::NEq(lhs, rhs) => AExpr::Eq(
                Box::new(lhs.var_change(callback.clone())),
                Box::new(rhs.var_change(callback.clone())),
            ),
            AExpr::And(vs) => AExpr::And(
                vs.into_iter()
                    .map(|e| e.var_change(callback.clone()))
                    .collect(),
            ),
            AExpr::Or(vs) => AExpr::Or(
                vs.into_iter()
                    .map(|e| e.var_change(callback.clone()))
                    .collect(),
            ),
            AExpr::Not(v) => AExpr::Not(Box::new(v.var_change(callback.clone()))),
            AExpr::IfThen(s, t) => AExpr::IfThen(
                Box::new(s.var_change(callback.clone())),
                Box::new(t.var_change(callback.clone())),
            ),
            AExpr::IfThenElse(s, t, e) => AExpr::IfThenElse(
                Box::new(s.var_change(callback.clone())),
                Box::new(t.var_change(callback.clone())),
                Box::new(e.var_change(callback.clone())),
            ),
            AExpr::Select(s, wt, wf) => AExpr::Select(
                Box::new(s.var_change(callback.clone())),
                Box::new(wt.var_change(callback.clone())),
                Box::new(wf.var_change(callback.clone())),
            ),
            AExpr::Query(var) => AExpr::Query(callback(var)),
        }
    }
}
