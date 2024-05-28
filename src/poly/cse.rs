use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use crate::{field::Field, sbpir::query::Queriable};

use std::{fmt::Debug, hash::Hash};

use super::{Expr, HashResult, VarAssignments};

/// Common Subexpression Elimination - takes a collection of expr
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: Vec<Expr<F, V, ()>>,
    queriables: &Vec<Queriable<F>>,
) -> Vec<Expr<F, V, HashResult>> {
    // generate random point in the field set
    let _assignments = generate_random_assignment(queriables);

    // hash all the functions using the point for the assignments

    // check if the hash is already in the hash table
    // if it is, then replace it by a reference to the other one

    // return the expressions hashed and optimized

    todo!()
}

fn generate_random_assignment<F: Field + Hash>(
    queriables: &Vec<Queriable<F>>,
) -> VarAssignments<F, String> {
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut assignments = VarAssignments::new();

    for queriable in queriables {
        let value = F::random(&mut rng);
        assignments.insert(queriable.annotation(), value);
    }

    assignments
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::sbpir::{query::Queriable, ForwardSignal, InternalSignal};

    #[test]
    fn test_generate_random_assignment() {
        let internal = InternalSignal::new("internal");
        let forward = ForwardSignal::new("forward");

        let a: Queriable<Fr> = Queriable::Internal(internal);
        let b: Queriable<Fr> = Queriable::Forward(forward, false);
        let c: Queriable<Fr> = Queriable::Forward(forward, true);

        let vars = vec![a, b, c];

        let keys: HashSet<Queriable<Fr>> = vars.iter().cloned().collect();

        let assignments = generate_random_assignment(&vars);

        println!("Assignments: {:#?}", assignments);

        for key in &keys {
            assert!(assignments.contains_key(&key.annotation()));
        }
    }

    #[test]
    fn test_cse() {
        todo!();
    }
}
