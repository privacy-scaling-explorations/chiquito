use halo2_proofs::arithmetic::Field;
use std::hash::Hash;

pub fn hadamard_product<F: Field + From<u64> + Hash>(vec1: &Vec<F>, vec2: &Vec<F>) -> Vec<F> {
    assert_eq!(vec1.len(), vec2.len());
    vec1.iter()
        .zip(vec2.iter())
        .map(|(&v1, &v2)| v1 * v2)
        .collect()
}

pub fn vec_add<F: Field + From<u64> + Hash>(vec: &Vec<Vec<F>>) -> Vec<F> {
    assert!(vec.len() > 1);
    vec.iter().fold(vec![F::ZERO; vec[0].len()], |acc, vec| {
        acc.iter().zip(vec.iter()).map(|(&a, &v)| a + v).collect()
    })
}

// input vector z = [1, x, w]
pub struct Z<F: Field + From<u64>> {
    n: usize,
    l: usize,
    values: Vec<F>,
}

impl<F: Field + From<u64> + Hash> Z<F> {
    pub fn new(n: usize, l: usize) -> Self {
        assert!(n > l);
        Self {
            n,
            l,
            values: Vec::new(),
        }
    }

    pub fn write(&mut self, inputs: &Vec<F>, witnesses: &Vec<F>) {
        assert_eq!(inputs.len(), self.l);
        assert_eq!(witnesses.len(), self.n - self.l - 1);

        // todo: order
        let mut witnesses = witnesses.clone();
        let mut inputs = inputs.clone();
        let mut values = vec![F::ONE];
        values.append(&mut inputs);
        values.append(&mut witnesses);
        self.values = values;
    }
}

pub struct Matrix<F> {
    n: usize,
    m: usize,
    values: Vec<Vec<F>>,
}

impl<F: Field + From<u64> + Hash> Matrix<F> {
    pub fn new(n: usize, m: usize) -> Self {
        Self {
            n,
            m,
            values: Vec::new(),
        }
    }

    pub fn write(&mut self, values: &[(usize, usize, F)]) {
        let mut matrix: Vec<Vec<F>> = (0..self.m)
            .map(|_| (0..self.n).map(|_| F::ZERO).collect())
            .collect();
        for &(row, col, value) in values.iter() {
            assert!(row < self.m);
            assert!(col < self.n);
            matrix[row][col] = value;
        }
        self.values = matrix.clone();
    }

    pub fn get(&self, row: usize, col: usize) -> F {
        assert!(row < self.m);
        assert!(col < self.n);
        self.values[row][col]
    }

    pub fn size(&self) -> (usize, usize) {
        (self.m, self.n)
    }
}

impl<F: Field + From<u64> + Hash> Matrix<F> {
    pub fn matrix_vector_product(&self, z: &Vec<F>) -> Vec<F> {
        (0..self.values.len())
            .map(|i| self.hadamard_product_and_sum(i, z))
            .collect()
    }

    fn hadamard_product_and_sum(&self, index: usize, z: &Vec<F>) -> F {
        assert!(index < self.values.len());
        assert_eq!(self.values[index].len(), z.len());
        hadamard_product(&self.values[index], z).iter().sum()
    }
}

pub struct CCSCircuit<F: Field + From<u64>> {
    n: usize,
    m: usize,
    nn: usize,
    l: usize,
    t: usize,
    q: usize,
    d: usize,
    matrices: Vec<Matrix<F>>,
    selectors: Vec<Vec<usize>>,
    constants: Vec<F>,
}

impl<F: Field + From<u64> + Hash> CCSCircuit<F> {
    pub fn new(n: usize, m: usize, t: usize, q: usize, l: usize) -> Self {
        assert!(n > l);

        let matrices = (0..t).map(|_| Matrix::new(n, m)).collect();

        let selectors = (0..q).map(|_| Vec::new()).collect();

        let constants = (0..q).map(|_| F::ZERO).collect();

        let nn = 0;

        Self {
            n,
            m,
            l,
            t,
            q,
            d: 0,
            nn,
            matrices,
            selectors,
            constants,
        }
    }

    pub fn read_nn(&self) -> usize {
        self.nn
    }

    pub fn public_num(&self) -> usize {
        self.l
    }

    pub fn witness_num(&self) -> usize {
        self.n - self.l - 1
    }

    pub fn write(
        &mut self,
        matrices: &Vec<Vec<(usize, usize, F)>>,
        selectors: &Vec<Vec<usize>>,
        constants: &Vec<F>,
    ) {
        let mut degree = 0;
        let mut nn = 0;

        assert_eq!(constants.len(), self.q);
        self.constants = constants.clone();

        assert_eq!(selectors.len(), self.q);
        for selector in selectors.iter() {
            for &s in selector {
                assert!(s < self.t)
            }
            degree = degree.max(selector.len())
        }
        self.selectors = selectors.clone();

        assert_eq!(matrices.len(), self.t);

        self.matrices = matrices
            .iter()
            .map(|cells| {
                for &cell in cells.iter() {
                    assert!(cell.0 < self.m);
                    assert!(cell.1 < self.n);
                    if cell.2 != F::ZERO {
                        nn += 1;
                    }
                }

                let mut matrix = Matrix::new(self.n, self.m);
                matrix.write(cells);
                matrix
            })
            .collect();

        self.d = degree;
        self.nn = nn;
    }

    pub fn is_satisfied(&self, z: &Z<F>) -> bool {
        assert_eq!(self.selectors.len(), self.q);
        assert_eq!(self.constants.len(), self.q);

        let prod_vec: Vec<Vec<F>> = self
            .constants
            .iter()
            .zip(self.selectors.iter())
            .map(|(&c, selector)| {
                let hadamard_prod_vec: Vec<Vec<F>> = selector
                    .iter()
                    .map(|&s| {
                        assert!(s < self.matrices.len());
                        self.matrices[s].matrix_vector_product(&z.values)
                    })
                    .collect();
                hadamard_prod_vec
                    .iter()
                    .fold(vec![c; self.m], |acc, vec| hadamard_product(&acc, vec))
            })
            .collect();
        let sum_vec = vec_add(&prod_vec);

        assert_eq!(sum_vec.len(), self.m);

        for &sum in sum_vec.iter() {
            if sum != F::ZERO {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_ccs() {
        let n = 7;
        let m = 4;
        let t = 8;
        let q = 5;
        let l = 3;

        let mut ccs_circuit: CCSCircuit<Fr> = CCSCircuit::new(n, m, t, q, l);
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

        let selectors = vec![vec![3, 0, 1], vec![4, 0], vec![5, 1], vec![6, 2], vec![7]];
        let constants: Vec<Fr> = vec![Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE];
        ccs_circuit.write(&matrices, &selectors, &constants);

        let mut z = Z::new(n, l);
        z.write(
            &vec![Fr::ZERO, Fr::ONE, Fr::from(2)],
            &vec![Fr::from(3), Fr::from(10), Fr::from(43)],
        );

        let result = ccs_circuit.is_satisfied(&z);

        println!("result = {}", result);
    }
}
