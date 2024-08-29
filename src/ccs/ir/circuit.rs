use std::hash::Hash;

use super::assignments::*;
use crate::field::Field;

// A multisets for selector in CCSCircuit
pub type SelectorsOffsetAndCoeff<F> = Vec<Vec<(usize, F)>>;

fn hadamard_product<F: Field + From<u64> + Hash>(vec1: &[F], vec2: &[F]) -> Vec<F> {
    assert_eq!(vec1.len(), vec2.len());
    vec1.iter()
        .zip(vec2.iter())
        .map(|(&v1, &v2)| v1 * v2)
        .collect()
}

fn vec_add<F: Field + From<u64> + Hash>(vec: &[Vec<F>]) -> Vec<F> {
    assert!(vec.len() > 1);
    vec.iter().fold(vec![F::ZERO; vec[0].len()], |acc, vec| {
        acc.iter().zip(vec.iter()).map(|(&a, &v)| a + v).collect()
    })
}

// Matrix
// n: The number of columns in one row
// m: The number of rows
// values: A two-dimensional vectors, where each sub vector represents a row of the matrix
#[derive(Debug, Clone)]
pub struct Matrix<F> {
    n: usize,
    m: usize,
    values: Vec<Vec<F>>,
}

impl<F: Field> Matrix<F> {
    // At the beginning, We can only get the numbers of rows and columns，
    // with all values being zero by default.
    pub fn new(n: usize, m: usize) -> Self {
        Self {
            n,
            m,
            values: vec![vec![F::ZERO; n]; m],
        }
    }

    // Modify parts of cells in a Matrix
    pub fn write(&mut self, values: &[(usize, usize, F)]) {
        for &(row, col, value) in values.iter() {
            assert!(row < self.m);
            assert!(col < self.n);
            self.values[row][col] = value;
        }
    }

    // Get all of the non-zero values in the matrices.
    pub fn from_values(n: usize, m: usize, values: &[(usize, usize, F)]) -> Self {
        let mut mvalues = vec![vec![F::ZERO; n]; m];
        for &(row, col, value) in values.iter() {
            assert!(row < m);
            assert!(col < n);
            mvalues[row][col] = value;
        }

        Self {
            n,
            m,
            values: mvalues,
        }
    }

    pub fn get(&self, row: usize, col: usize) -> F {
        assert!(row < self.m);
        assert!(col < self.n);
        self.values[row][col]
    }

    pub fn reduce_rows(&mut self, m: usize) {
        if m < self.m {
            self.values.truncate(m);
            self.m = m;
        }
    }

    pub fn size(&self) -> (usize, usize) {
        (self.m, self.n)
    }

    pub fn values(&self) -> Vec<Vec<F>> {
        self.values.clone()
    }
}

impl<F: Field + From<u64> + Hash> Matrix<F> {
    pub fn matrix_vector_product(&self, z: &[F]) -> Vec<F> {
        (0..self.values.len())
            .map(|i| self.hadamard_product_and_sum(i, z))
            .collect()
    }

    fn hadamard_product_and_sum(&self, index: usize, z: &[F]) -> F {
        assert!(index < self.values.len());
        assert_eq!(self.values[index].len(), z.len());
        hadamard_product(&self.values[index], z).iter().sum()
    }
}

// CCS Circuit
// n: The number of columns in one row, as well as the length of all the assignments
// m: The number of rows
// l: The number of public inputs
// t: The number of matrices
// q: The number of multisets, where
// d: The degree of each multiset is at most d.
// matrices: all of the matrices
// selectors: a sequence of q multisets, where an element in each multiset is the index of a matrix
// constants: q constants for q multisets
#[derive(Debug, Default)]
pub struct CCSCircuit<F> {
    pub n: usize,
    pub m: usize,
    pub l: usize,
    pub t: usize,
    pub q: usize,
    pub d: usize,
    pub matrices: Vec<Matrix<F>>,
    pub selectors: SelectorsOffsetAndCoeff<F>,
    pub constants: Vec<F>,
}

impl<F: Field + From<u64> + Hash> CCSCircuit<F> {
    pub fn public_num(&self) -> usize {
        self.l
    }

    pub fn witness_num(&self) -> usize {
        self.n - self.l - 1
    }

    pub fn is_satisfied(&self, z: &Z<F>) -> bool {
        assert_eq!(self.selectors.len(), self.q);
        assert_eq!(self.constants.len(), self.q);

        let mut witnesses = z.witnesses.clone();
        let mut inputs = z.public_inputs.clone();

        let mut values = vec![F::ONE];
        values.append(&mut inputs);
        values.append(&mut witnesses);

        let prod_vec: Vec<Vec<F>> = self
            .constants
            .iter()
            .zip(self.selectors.iter())
            .map(|(&c, selector)| {
                let hadamard_prod_vec: Vec<Vec<F>> = selector
                    .iter()
                    .map(|&(s, _)| {
                        assert!(s < self.matrices.len());
                        self.matrices[s].matrix_vector_product(&values)
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
