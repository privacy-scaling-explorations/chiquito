use std::sync::atomic::{AtomicU32, Ordering};

static UUID_GEN: AtomicU32 = AtomicU32::new(1);

pub fn uuid() -> u32 {
    UUID_GEN.fetch_add(1, Ordering::SeqCst)
}
