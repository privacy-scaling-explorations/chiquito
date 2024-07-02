pub(super) fn cse(
    mut circuit: SBPIR<F, NullTraceGenerator>,
) -> SBPIR<F, NullTraceGenerator> {
    let mut cse = CSE::default();
    cse.run(&mut circuit);
    circuit
}

struct CSE {
    // The current circuit being optimized
    circuit: SBPIR<F, NullTraceGenerator>,
    // The current circuit being optimized
    cse: HashMap<String, Expr<F, V, HashResult>>,
}

