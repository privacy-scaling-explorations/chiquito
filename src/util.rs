use std::sync::atomic::{AtomicU32, Ordering};

use halo2_proofs::{arithmetic::Field, halo2curves::FieldExt};

use crate::{
    ast::{query::Queriable, ToExpr, Expr},
};

static UUID_GEN: AtomicU32 = AtomicU32::new(1);

pub fn uuid() -> u32 {
    UUID_GEN.fetch_add(1, Ordering::SeqCst)
}

/// Given a bytes-representation of an expression, it computes and returns the
/// single expression.
pub fn expr_from_bytes<F: FieldExt>(bytes: Vec<Queriable<F>>) -> Expr<F> {
    let mut value = 0u64.expr();
    let mut multiplier = Expr::from(1);
    for byte in bytes.iter() {
        value = value + byte.expr() * multiplier;
        multiplier = multiplier * Expr::from(256);
    }
    value
}
