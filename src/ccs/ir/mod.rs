use std::{collections::HashMap, fmt::Debug};

pub mod assignments;
pub mod circuit;

use crate::{field::Field, poly::Expr, util::UUID};

#[derive(Clone)]
pub struct Poly<F> {
    pub uuid: UUID,
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

pub type Coeff<F> = (F, UUID, bool);
pub type Coeffs<F> = Vec<Coeff<F>>;
pub type CoeffsForProds<F> = Vec<Coeffs<F>>;
pub type CoeffsOnePoly<F> = Vec<CoeffsForProds<F>>;
pub type CoeffsOneStep<F> = Vec<CoeffsOnePoly<F>>;
pub type CoeffsForSteps<F> = HashMap<UUID, CoeffsOneStep<F>>;

pub type MatrixsCoeffs<F> = Vec<Vec<(CoeffsForProds<F>, usize)>>;

impl<F: Field> PolyExpr<F> {
    pub fn poly_to_coeffs(&self, flag: bool) -> CoeffsOnePoly<F> {
        let matrics = match self {
            PolyExpr::Const(v) => vec![vec![vec![(*v, 0, false)]]],
            PolyExpr::Query((id, _, _, q)) => vec![vec![vec![(F::ONE, *id, *q)]]],
            PolyExpr::Neg(v) => {
                let mut coeffs_for_one_poly = v.poly_to_coeffs(flag);
                for coeffs_for_prods in coeffs_for_one_poly.iter_mut() {
                    coeffs_for_prods.push(vec![(F::ONE.neg(), 0, false)]);
                }
                coeffs_for_one_poly
            }
            PolyExpr::Sum(v) => {
                if flag {
                    let mut coeffs_for_one_poly: Vec<CoeffsForProds<F>> = Vec::new();
                    for e in v.iter() {
                        coeffs_for_one_poly.append(&mut e.poly_to_coeffs(false));
                    }
                    coeffs_for_one_poly
                } else {
                    let coeffs = v
                        .iter()
                        .map(|e| match *e {
                            PolyExpr::Const(v) => (v, 0, false),
                            PolyExpr::Query((id, _, _, q)) => (F::ONE, id, q),
                            PolyExpr::Neg(_) => (F::ONE.neg(), 0, false),
                            _ => panic!("invalid poly expr"),
                        })
                        .collect();
                    vec![vec![coeffs]]
                }
            }
            PolyExpr::Mul(v) => {
                let mut matrics = Vec::new();
                for e in v.iter() {
                    let matrix = e.poly_to_coeffs(false);
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
                let coeffs = v.poly_to_coeffs(flag);
                if coeffs.len() != 1 {
                    panic!("invalid poly expr");
                }
                (0..*exp)
                    .map(|_| coeffs.clone())
                    .collect::<Vec<_>>()
                    .concat()
            }
            _ => panic!("invalid poly expr"),
        };
        matrics
    }
}
