use std::sync::atomic::{AtomicU32, Ordering};

use halo2_proofs::arithmetic::Field;

use crate::ast::{query::Queriable, Expr, ToExpr};

static UUID_GEN: AtomicU32 = AtomicU32::new(1);

pub fn uuid() -> u32 {
    UUID_GEN.fetch_add(1, Ordering::SeqCst)
}

/// Given a bytes-representation of an expression, it computes and returns the
/// single expression.
pub fn expr_from_bytes<F: Field + From<u64>>(bytes: Vec<Queriable<F>>) -> Expr<F> {
    let mut value = 0u64.expr();
    let mut multiplier = 1u64.expr();
    for byte in bytes.iter() {
        value = value + byte.expr() * multiplier.clone();
        multiplier = multiplier * 256u64.expr();
    }
    value
}
