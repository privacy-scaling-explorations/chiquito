use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

use crate::field::Field;

use std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    rc::{Rc, Weak},
};

use super::{Expr, HashResult, VarAssignments};

/// Common Subexpression Elimination - takes a collection of expr
pub fn cse<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    exprs: Vec<Expr<F, V, ()>>,
    queriables: &Vec<V>,
) -> Vec<Rc<Expr<F, V, HashResult>>> {
    // generate random point in the field set
    let assignments = generate_random_assignment(queriables);

    // hash table with the hash of the expression as the key
    // and the weak reference to the expression as the value
    let mut seen_hashes: HashMap<u64, Weak<Expr<F, V, HashResult>>> = HashMap::new();

    let mut result = Vec::new();

    for expr in exprs {
        let hashed_expr = Rc::new(expr.hash(&assignments));
        let hash = hashed_expr.meta().hash;

        // if the hash is already in the hash table,
        // push the existing expression to the result
        if let Some(existing_weak) = seen_hashes.get(&hash) {
            if let Some(existing_expr) = existing_weak.upgrade() {
                result.push(existing_expr);
                continue;
            }
        }

        // otherwise, insert the hash and the weak reference to the expression
        seen_hashes.insert(hash, Rc::downgrade(&hashed_expr));
        result.push(hashed_expr);
    }

    result
}

fn generate_random_assignment<F: Field + Hash, V: Debug + Clone + Eq + Hash>(
    queriables: &Vec<V>,
) -> VarAssignments<F, V> {
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut assignments = HashMap::new();

    for queriable in queriables {
        let value = F::random(&mut rng);
        assignments.insert(queriable.clone(), value);
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

        let assignments: VarAssignments<Fr, Queriable<Fr>> = generate_random_assignment(&vars);

        println!("Assignments: {:#?}", assignments);

        for key in &keys {
            assert!(assignments.contains_key(&key));
        }
    }

    #[test]
    fn test_cse() {
        let internal = InternalSignal::new("internal");
        let forward = ForwardSignal::new("forward");

        let a: Queriable<Fr> = Queriable::Internal(internal);
        let b: Queriable<Fr> = Queriable::Forward(forward, false);
        let c: Queriable<Fr> = Queriable::Forward(forward, true);
        let d: Queriable<Fr> = Queriable::Forward(forward, true);

        let vars = vec![a, b, c];

        let expr1 = a + b;
        let expr2 = a + c;
        let expr3 = a + d;

        let exprs = vec![expr1, expr2, expr3];

        let result = cse(exprs, &vars);

        assert!(Rc::ptr_eq(&result[1], &result[2]));
        assert!(Rc::ptr_eq(&result[0], &result[1]) == false);
    }
}
