use crate::{field::Field, poly::Expr, util::UUID};
use std::{collections::HashMap, fmt::Debug, hash::Hash};
pub mod assignments;
pub mod circuit;

use assignments::Assignments;
use circuit::CCSCircuit;

pub type MatrixCoeffsAndOffset<F> = Vec<Vec<(CoeffsForProds<F>, usize)>>;

// Use to mark the public inputs
// ((step_idx, step_UUID), assignment_offset)
pub type AssignmentOffsets = HashMap<(usize, u128), usize>;

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

// (signal_uuid, step_uuid, annotation, is_next)
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

// Circuit
// matrix_coeffs_and_offsets: Temporarily record all circuit coefficients in each step
//                          (It is not possible to build a complete circuit until the trace is
// traced,                          so it is necessary to temporarily record the circuit structure
// in each step.) exposed: All the offsets of public inputs
// witness: All the offsets of the witnesses
// ccs: The ccs circuit
#[derive(Debug)]
pub struct Circuit<F> {
    pub ast_id: UUID,

    pub matrix_coeffs_and_offsets: HashMap<UUID, MatrixCoeffsAndOffset<F>>,
    pub exposed: Vec<(usize, UUID)>,
    pub witness: HashMap<UUID, Vec<UUID>>,

    pub ccs: CCSCircuit<F>,
}

impl<F: Field + From<u64> + Hash> Circuit<F> {
    pub fn instance(&self, assignments: &Option<Assignments<F>>) -> HashMap<(usize, UUID), F> {
        let mut exposes = HashMap::new();
        if !self.exposed.is_empty() {
            for (step_idx, id) in self.exposed.iter() {
                if let Some(witness) = assignments {
                    exposes.insert((*step_idx, *id), witness.get(*step_idx, *id));
                }
            }
        }
        exposes
    }
}
#[cfg(test)]
mod tests {
    use std::vec;

    use super::{assignments::Z, circuit::Matrix, *};
    use halo2_proofs::halo2curves::bn256::Fr;

    fn create_ccs_circuit<F: Field + From<u64> + Hash>(
        n: usize,
        m: usize,
        l: usize,
        matrices: &[Vec<(usize, usize, F)>],
        selectors: &[Vec<(usize, F)>],
        constants: &[F],
    ) -> CCSCircuit<F> {
        let mut degree = 0;
        assert_eq!(selectors.len(), constants.len());
        for selector in selectors.iter() {
            for &(s, _) in selector {
                assert!(s < matrices.len())
            }
            degree = degree.max(selector.len())
        }
        let matrices: Vec<Matrix<F>> = matrices
            .iter()
            .map(|cells| Matrix::from_values(n, m, cells))
            .collect();

        CCSCircuit {
            n,
            m,
            t: matrices.len(),
            q: constants.len(),
            l,
            d: degree,
            constants: constants.to_vec(),
            selectors: selectors.to_vec(),
            matrices,
        }
    }

    #[test]
    fn test_ccs() {
        let n = 7;
        let m = 4;
        let l = 3;

        let m0 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 3, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m1 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 4, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m2 = vec![
            (0, 1, Fr::ONE),
            (1, 2, Fr::ONE),
            (2, 5, Fr::ONE),
            (3, 6, Fr::ONE),
        ];
        let m3 = vec![(0, 0, Fr::ONE), (1, 0, Fr::ONE)];
        let m4 = vec![(2, 0, Fr::from(2))];
        let m5 = vec![(2, 0, Fr::from(2))];
        let m6 = vec![
            (0, 0, Fr::ONE.neg()),
            (1, 0, Fr::ONE.neg()),
            (2, 0, Fr::ONE.neg()),
        ];
        let m7 = vec![(0, 0, Fr::ZERO)];
        let matrices = vec![m0, m1, m2, m3, m4, m5, m6, m7];

        let selectors = vec![
            vec![(3, Fr::ONE), (0, Fr::ONE), (1, Fr::ONE)],
            vec![(4, Fr::ONE), (0, Fr::ONE)],
            vec![(5, Fr::ONE), (1, Fr::ONE)],
            vec![(6, Fr::ONE), (2, Fr::ONE)],
            vec![(7, Fr::ONE)],
        ];
        let constants: Vec<Fr> = vec![Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE];

        let ccs_circuit = create_ccs_circuit(n, m, l, &matrices, &selectors, &constants);

        let z = Z::from_values(
            &[Fr::ZERO, Fr::ONE, Fr::from(2)],
            &[Fr::from(3), Fr::from(10), Fr::from(43)],
        );

        let result = ccs_circuit.is_satisfied(&z);

        println!("result = {}", result);
    }
}
