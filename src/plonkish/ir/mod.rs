use std::{fmt::Debug, hash::Hash};

use halo2_proofs::plonk::Expression;

use crate::{
    ast::{ImportedHalo2Advice, ImportedHalo2Fixed},
    util::{uuid, UUID},
};

use self::assignments::Assignments;

pub mod assignments;
pub mod sc;

#[derive(Clone, Default)]
pub struct Circuit<F> {
    pub columns: Vec<Column>,
    pub exposed: Vec<(Column, i32)>,

    pub polys: Vec<Poly<F>>,
    pub lookups: Vec<PolyLookup<F>>,

    pub fixed_assignments: Assignments<F>,

    pub id: UUID,
    pub ast_id: UUID,
}

impl<F: Debug> Debug for Circuit<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Circuit")
            .field("columns", &self.columns)
            .field("polys", &self.polys)
            .field("lookups", &self.lookups)
            .finish()
    }
}

#[derive(Clone, Debug, Hash)]
pub enum ColumnType {
    Advice,
    Fixed,
    Halo2Advice,
    Halo2Fixed,
}

#[derive(Clone, Debug)]
pub struct Column {
    pub annotation: String,

    pub ctype: ColumnType,
    pub halo2_advice: Option<ImportedHalo2Advice>,
    pub halo2_fixed: Option<ImportedHalo2Fixed>,

    pub phase: usize,

    pub(crate) id: UUID,
}

impl Column {
    pub fn advice<A: Into<String>>(annotation: A, phase: usize) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            ctype: ColumnType::Advice,
            phase,
            halo2_advice: None,
            halo2_fixed: None,
        }
    }

    pub fn fixed<A: Into<String>>(annotation: A) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            ctype: ColumnType::Fixed,
            phase: 0,
            halo2_advice: None,
            halo2_fixed: None,
        }
    }

    pub fn new_halo2_advice<A: Into<String>>(
        annotation: A,
        halo2_advice: ImportedHalo2Advice,
    ) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            phase: 0,
            ctype: ColumnType::Halo2Advice,
            halo2_advice: Some(halo2_advice),
            halo2_fixed: None,
        }
    }

    pub fn new_halo2_fixed<A: Into<String>>(
        annotation: A,
        halo2_fixed: ImportedHalo2Fixed,
    ) -> Column {
        Column {
            annotation: annotation.into(),
            id: uuid(),
            phase: 0,
            ctype: ColumnType::Halo2Fixed,
            halo2_advice: None,
            halo2_fixed: Some(halo2_fixed),
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }
}

impl PartialEq for Column {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for Column {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Eq for Column {}

#[derive(Clone)]
pub struct Poly<F> {
    pub annotation: String,
    pub expr: PolyExpr<F>,
}

impl<F: Debug> Debug for Poly<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => {:?}", self.annotation, self.expr)
    }
}

#[derive(Clone)]
pub enum PolyExpr<F> {
    Const(F),
    Query(Column, i32, String), // column, rotation, annotation
    Sum(Vec<PolyExpr<F>>),
    Mul(Vec<PolyExpr<F>>),
    Neg(Box<PolyExpr<F>>),
    Pow(Box<PolyExpr<F>>, u32),
    Halo2Expr(Expression<F>),
}

impl<F: Debug> Debug for PolyExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let joiner = |list: &Vec<PolyExpr<F>>, sep: &str| {
            list.iter()
                .map(|v| format!("{:?}", v))
                .collect::<Vec<String>>()
                .join(sep)
        };

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
            Self::Query(_, _, annotation) => write!(f, "`{}`", annotation),
            Self::Sum(arg0) => write!(f, "({})", joiner(arg0, " + ")),
            Self::Mul(arg0) => write!(f, "({})", joiner(arg0, " * ")),
            Self::Neg(arg0) => write!(f, "(-{:?})", arg0),
            Self::Pow(arg0, arg1) => f.debug_tuple("Pow").field(arg0).field(arg1).finish(),
            Self::Halo2Expr(expr) => write!(f, "{:?}", expr),
        }
    }
}

impl<F: Clone> PolyExpr<F> {
    pub fn rotate(&self, rot: i32) -> PolyExpr<F> {
        match self {
            PolyExpr::Const(_) => (*self).clone(),
            PolyExpr::Query(c, orig_rot, annotation) => PolyExpr::Query(
                c.clone(),
                orig_rot + rot,
                format!("rot[{}, {}]", rot, annotation),
            ),
            PolyExpr::Sum(v) => PolyExpr::Sum(v.iter().map(|e| e.rotate(rot)).collect()),
            PolyExpr::Mul(v) => PolyExpr::Mul(v.iter().map(|e| e.rotate(rot)).collect()),
            PolyExpr::Neg(v) => PolyExpr::Neg(Box::new(v.rotate(rot))),
            PolyExpr::Pow(v, exp) => PolyExpr::Pow(Box::new(v.rotate(rot)), *exp),
            PolyExpr::Halo2Expr(_) => panic!("jarrl: cannot rotate polyexpr that contains halo2"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PolyLookup<F> {
    pub annotation: String,
    pub exprs: Vec<(PolyExpr<F>, PolyExpr<F>)>,
}

#[cfg(test)]
mod tests {
    use super::PolyExpr;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_poly_expr_fmt() {
        let a: Fr = 10.into();
        let b: Fr = 20.into();

        let expr1 = PolyExpr::Const(&a);
        assert_eq!(format!("{:?}", expr1), "0xa");

        let expr2 = PolyExpr::Sum(vec![PolyExpr::Const(&a), PolyExpr::Const(&b)]);
        assert_eq!(format!("{:?}", expr2), "(0xa + 0x14)");

        let expr3 = PolyExpr::Mul(vec![PolyExpr::Const(&a), PolyExpr::Const(&b)]);
        assert_eq!(format!("{:?}", expr3), "(0xa * 0x14)");

        let expr4 = PolyExpr::Neg(Box::new(PolyExpr::Const(&a)));
        assert_eq!(format!("{:?}", expr4), "(-0xa)");

        let expr5 = PolyExpr::Pow(Box::new(PolyExpr::Const(&a)), 2);
        assert_eq!(format!("{:?}", expr5), "Pow(0xa, 2)");
    }
}
