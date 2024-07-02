use crate::field::Field;

use std::{fmt::Debug, hash::Hash};

use super::{ConstrDecomp, Expr, HashResult, SignalFactory, VarAssignments};

pub fn replace_common_subexprs<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    constr: Expr<F, V, ()>,
    common_ses: &[Expr<F, V, HashResult>],
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> (Expr<F, V, ()>, ConstrDecomp<F, V>) {
    let mut decomp = ConstrDecomp::default();
    let expr =
        replace_common_subexprs_rec(&mut decomp, constr, common_ses, assignments, signal_factory);

    (expr, decomp)
}

fn replace_common_subexprs_rec<
    F: Field + Hash,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V, ()>,
    common_ses: &[Expr<F, V, HashResult>],
    assignments: &VarAssignments<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V, ()> {
    // Check if the expression is a common subexpression
    if let Some(_common_expr) = common_ses
        .iter()
        .find(|ce| constr.hash(assignments).meta().hash == ce.meta().hash)
    {
        // If it is, check if the signal already exists
        let hash = constr.hash(assignments).meta().hash;
        if let Some(signal) = decomp.auto_signals.iter().find_map(|(signal, expr)| {
            if expr.hash(assignments).meta().hash == hash {
                Some(signal.clone())
            } else {
                None
            }
        }) {
            Expr::Query(signal, ())
        } else {
            let new_signal = signal_factory.create("cse");
            decomp.auto_eq(new_signal.clone(), constr);
            Expr::Query(new_signal, ())
        }
    } else {
        // Otherwise, replace the subexpressions recursively
        match constr {
            Expr::Sum(ses, meta) => {
                let new_ses = ses
                    .into_iter()
                    .map(|se| {
                        replace_common_subexprs_rec(
                            decomp,
                            se,
                            common_ses,
                            assignments,
                            signal_factory,
                        )
                    })
                    .collect();
                Expr::Sum(new_ses, meta)
            }
            Expr::Mul(ses, meta) => {
                let new_ses = ses
                    .into_iter()
                    .map(|se| {
                        replace_common_subexprs_rec(
                            decomp,
                            se,
                            common_ses,
                            assignments,
                            signal_factory,
                        )
                    })
                    .collect();
                Expr::Mul(new_ses, meta)
            }
            Expr::Neg(se, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::Neg(Box::new(new_se), meta)
            }
            Expr::Pow(se, n, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::Pow(Box::new(new_se), n, meta)
            }
            Expr::MI(se, meta) => {
                let new_se = replace_common_subexprs_rec(
                    decomp,
                    *se,
                    common_ses,
                    assignments,
                    signal_factory,
                );
                Expr::MI(Box::new(new_se), meta)
            }
            _ => constr,
        }
    }
}
