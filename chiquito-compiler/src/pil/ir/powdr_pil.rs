use crate::pil::compiler::{PILColumn, PILExpr, PILQuery};
use std::collections::HashMap;
extern crate regex;

// PIL circuit IR
pub struct PILCircuit<F> {
    pub circuit_name: String,
    pub num_steps: usize,
    pub col_witness: Vec<PILColumn>,
    pub col_fixed: HashMap<PILColumn, Vec<F>>, // column -> assignments
    pub constraints: Vec<PILExpr<F, PILQuery>>,
    pub lookups: Vec<PILLookup>,
}

// lookup in PIL is the format of selector {src1, src2, ..., srcn} -> {dst1, dst2, ..., dstn}
// PILLookup is a tuple of (selector, Vec<src, dst>) tuples, where selector is converted from
// Chiquito step type to fixed column
pub type PILLookup = (PILColumn, Vec<(PILColumn, PILColumn)>);
