use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use crate::field::Field;

use std::{collections::HashSet, fmt::Debug, hash::Hash};

use super::{Expr, HashResult, VarAssignments};

/// Common Subexpression Elimination - takes a collection of expr
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: Vec<Expr<F, V, ()>>,
) -> Vec<Expr<F, V, HashResult>> {
    // get the key set for the assignments
    let mut keys: HashSet<V> = HashSet::new();

    for expr in exprs.iter() {
        // get the assignments for the expression
        let expr_queries = expr.get_queries();
        // add the assignments to the key set
        keys.extend(expr_queries);
    }
    // generate random point in the field set
    let _assignments = generate_random_assignment::<F, V>(keys);

    // hash all the functions using the point for the assignments

    // check if the hash is already in the hash table
    // if it is, then replace it by a reference to the other one

    // return the expressions hashed and optimized

    todo!()
}

fn generate_random_assignment<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    keys: HashSet<V>,
) -> VarAssignments<F, V> {
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut assignments = VarAssignments::new();

    for key in keys.iter() {
        let value = F::random(&mut rng);
        assignments.insert(key.clone(), value);
    }

    assignments
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::sbpir::{query::Queriable, InternalSignal};

    #[test]
    fn test_generate_random_assignment() {
        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));
        let g: Queriable<Fr> = Queriable::Internal(InternalSignal::new("g"));
        let vars = vec![a, b, c, d, e, f, g];

        let keys: HashSet<Queriable<Fr>> = vars.iter().cloned().collect();

        let assignments = generate_random_assignment::<Fr, Queriable<Fr>>(keys.clone());

        for key in &keys {
            assert!(assignments.contains_key(key));
        }
    }

    #[test]
    fn test_cse() {
        todo!()
    }
}
