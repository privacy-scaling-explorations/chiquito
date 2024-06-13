use std::fmt::Debug;

pub mod assignments;
pub mod circuit;

use crate::{field::Field, poly::Expr, util::UUID};

#[derive(Clone)]
pub struct Poly<F> {
    pub step_uuid: UUID,
    pub annotation: String,
    pub expr: PolyExpr<F>,
}

impl<F: Debug> Debug for Poly<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => {:?}", self.annotation, self.expr)
    }
}

// (signal_uuid, step_uuid, annotation, pos)
pub type PolyExpr<F> = Expr<F, (UUID, UUID, String, bool)>;

impl<F: Field> PolyExpr<F> {
    pub fn poly_to_matrix(&self, flag: bool) -> Vec<Vec<Vec<(F, UUID, bool)>>> {
        let matrics = match self {
            PolyExpr::Const(v) => vec![vec![vec![(*v, 0, false)]]],
            PolyExpr::Query((id, _, _, q)) => vec![vec![vec![(F::ONE, *id, *q)]]],
            PolyExpr::Neg(v) => {
                let mut matrics = v.poly_to_matrix(flag);
                for matrixs in matrics.iter_mut() {
                    matrixs.push(vec![(F::ONE.neg(), 0, false)]);
                }
                matrics
            }
            PolyExpr::Sum(v) => {
                if flag {
                    let mut matrics = Vec::new();
                    for e in v.iter() {
                        matrics.append(&mut e.poly_to_matrix(false));
                    }
                    matrics
                } else {
                    let values = v
                        .iter()
                        .map(|e| match *e {
                            PolyExpr::Const(v) => (v, 0, false),
                            PolyExpr::Query((id, _, _, q)) => (F::ONE, id, q),
                            PolyExpr::Neg(_) => (F::ONE.neg(), 0, false),
                            _ => panic!("invalid poly expr"),
                        })
                        .collect();
                    vec![vec![values]]
                }
            }
            PolyExpr::Mul(v) => {
                let mut matrics = Vec::new();
                for e in v.iter() {
                    let matrix = e.poly_to_matrix(false);
                    if matrix.len() != 1 {
                        panic!("invalid poly expr");
                    }
                    for m in matrix[0].iter() {
                        matrics.push(m.clone());
                    }
                }
                vec![matrics]
            }
            PolyExpr::Pow(v, exp) => {
                let matrics = v.poly_to_matrix(flag);
                if matrics.len() != 1 {
                    panic!("invalid poly expr");
                }
                (0..*exp)
                    .map(|_| matrics.clone())
                    .collect::<Vec<_>>()
                    .concat()
            }
            _ => panic!("invalid poly expr"),
        };
        matrics
    }
}
