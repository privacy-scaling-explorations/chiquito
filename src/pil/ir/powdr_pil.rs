use crate::{ast::query::Queriable, poly::Expr, util::UUID};
use std::collections::HashMap;
extern crate regex;

// PIL circuit IR
pub struct PilCircuit<F> {
    // circuit level
    pub circuit_name: String,
    pub num_steps: usize,

    // circuit level - col witness
    pub col_witness: Vec<UUID>, // internal signal NOT dedupped

    // circuit level - col fixed
    pub fixed_signals: HashMap<UUID, Vec<F>>, // fixed signal UUID -> fixed assignments vector
    pub step_types_instantiations: HashMap<UUID, Vec<usize>>, /* step type UUID -> step
                                               * instances
                                               * vector {0, 1}^num_steps */
    pub first_step: Option<UUID>,
    pub last_step: Option<UUID>,

    // step type level
    pub step_types: Vec<UUID>,
    pub constraints: HashMap<UUID, Vec<Expr<F, Queriable<F>>>>, // step type UUID -> constraints
    pub transitions: HashMap<UUID, Vec<Expr<F, Queriable<F>>>>,
    pub lookups: HashMap<UUID, Vec<PilLookup<F>>>, // step type UUID -> lookups vector
}

pub type PilLookup<F> = Vec<(Expr<F, Queriable<F>>, Expr<F, Queriable<F>>)>;
