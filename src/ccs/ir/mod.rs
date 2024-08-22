use std::{collections::HashMap, fmt::Debug};

use crate::{field::Field, poly::Expr, util::UUID};
pub mod assignments;
pub mod circuit;

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

impl<F: Field> PolyExpr<F> {
    pub fn poly_to_coeffs(&self) -> CoeffsOnePoly<F> {
        let matrices = match self {
            PolyExpr::Const(v) => vec![vec![vec![(*v, 0, false)]]],
            PolyExpr::Query((id, _, _, q)) => vec![vec![vec![(F::ONE, *id, *q)]]],
            PolyExpr::Sum(v) => {
                let mut flag = true;
                for v in v.iter() {
                    flag = match v {
                        Expr::Const(_) => flag,
                        Expr::Query(_) => flag,
                        _ => false,
                    };
                    if !flag {
                        break;
                    }
                }
                if !flag {
                    let mut coeffs_for_one_poly: Vec<CoeffsForProds<F>> = Vec::new();
                    for e in v.iter() {
                        coeffs_for_one_poly.append(&mut e.poly_to_coeffs());
                    }
                    coeffs_for_one_poly
                } else {
                    let mut coeffs: HashMap<(UUID, bool), F> = HashMap::new();
                    for e in v.iter() {
                        if let Expr::Const(v) = e {
                            match coeffs.get(&(0, false)) {
                                None => coeffs.insert((0, false), *v),
                                Some(&value) => {
                                    let v = value + *v;
                                    coeffs.insert((0, false), v)
                                }
                            };
                        } else if let Expr::Query((id, _, _, q)) = e {
                            match coeffs.get(&(*id, *q)) {
                                None => coeffs.insert((*id, *q), F::ONE),
                                Some(&value) => {
                                    let v = value + F::ONE;
                                    coeffs.insert((*id, *q), v)
                                }
                            };
                        }
                    }
                    let coeffs = coeffs.iter().map(|((id, q), v)| (*v, *id, *q)).collect();
                    vec![vec![coeffs]]
                }
            }
            PolyExpr::Mul(v) => {
                let mut matrices = Vec::new();
                for e in v.iter() {
                    let matrix = e.poly_to_coeffs();
                    if matrix.len() != 1 {
                        panic!("[poly_to_coeffs]invalid poly expr with PolyExpr::Mul");
                    }
                    for m in matrix[0].iter() {
                        matrices.push(m.clone());
                    }
                }
                vec![matrices]
            }
            _ => panic!("[poly_to_coeffs]invalid poly expr"),
        };
        matrices
    }

    pub fn factor_expr(&self) -> PolyExpr<F> {
        let poly = self.pre_factor();
        poly.factor()
    }

    fn pre_factor(&self) -> PolyExpr<F> {
        match self {
            Expr::Const(_) => self.clone(),
            Expr::Query(_) => self.clone(),
            Expr::Sum(v) => PolyExpr::Sum(v.iter().map(|e| e.pre_factor()).collect()),
            Expr::Neg(v) => PolyExpr::Mul(vec![v.pre_factor(), Expr::Const(F::ONE.neg())]),
            Expr::Pow(v, exp) => {
                let v = v.pre_factor();
                PolyExpr::Mul(vec![v; *exp as usize])
            }
            Expr::Mul(v) => PolyExpr::Mul(v.iter().map(|e| e.pre_factor()).collect()),
            Expr::Halo2Expr(_) => panic!("halo2 expr not done"),
            Expr::MI(_) => panic!("mi elimination not done"),
        }
    }

    fn factor(&self) -> PolyExpr<F> {
        match self {
            Expr::Const(_) => self.clone(),
            Expr::Query(_) => self.clone(),
            Expr::Sum(v) => PolyExpr::Sum(v.iter().map(|e| e.factor()).collect()),
            Expr::Mul(v) => {
                let v: Vec<PolyExpr<F>> = v.iter().map(|e| e.factor()).collect();
                factor_mul(v)
            }
            _ => panic!("invalid expr"),
        }
    }
}

fn factor_mul<F: Clone + Field>(polys: Vec<PolyExpr<F>>) -> PolyExpr<F> {
    let mut sum_polys = Vec::new();
    let mut no_sum_polys = Vec::new();
    for v in polys.iter() {
        if let Expr::Sum(_) = v {
            sum_polys.push(v.clone());
        } else {
            no_sum_polys.push(v.clone());
        }
    }
    let mut new_polys = PolyExpr::Mul(no_sum_polys);

    for poly in sum_polys.iter() {
        if let PolyExpr::Sum(poly_vec) = poly {
            new_polys = match new_polys {
                Expr::Mul(v) => {
                    let polys: Vec<PolyExpr<F>> = poly_vec
                        .iter()
                        .map(|e| {
                            let mut v = v.clone();
                            v.push(e.clone());
                            Expr::Mul(v)
                        })
                        .collect();
                    PolyExpr::Sum(polys)
                }
                Expr::Sum(v_vec) => {
                    let polys: Vec<Vec<PolyExpr<F>>> = v_vec
                        .iter()
                        .map(|v| {
                            poly_vec
                                .iter()
                                .map(|e| Expr::Mul(vec![v.clone(), e.clone()]))
                                .collect()
                        })
                        .collect();
                    PolyExpr::Sum(polys.concat())
                }
                _ => panic!("invalid expr"),
            };
        }
    }

    new_polys
}
