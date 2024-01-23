use core::fmt::Debug;

pub mod expression;
pub mod statement;
pub mod tl;

// TODO: scafolding struct that should be implemented fully
#[derive(Clone, Debug)]
pub struct DebugSymRef {
    pub start: usize,
    pub end: usize,
}

impl DebugSymRef {
    pub fn new(start: usize, end: usize) -> DebugSymRef {
        DebugSymRef { start, end }
    }
}

pub struct Variable(pub String, pub i32);

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 == 0 {
            write!(f, "{}", self.0)
        } else {
            write!(f, "{}#{}", self.0, self.1)
        }
    }
}
