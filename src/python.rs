use crate::{
    ast::Circuit,
    frontend::pychiquito::{chiquito_ast_to_halo2, chiquito_halo2_mock_prover},
    wit_gen::TraceWitness,
};
use halo2_proofs::halo2curves::bn256::Fr;
use pyo3::{
    prelude::*,
    types::{PyLong, PyString},
};

#[pyfunction]
fn convert_and_print_ast(json: &PyString) {
    let circuit: Circuit<Fr, ()> =
        serde_json::from_str(json.to_str().expect("PyString convertion failed."))
            .expect("Json deserialization to Circuit failed.");
    println!("{:?}", circuit);
}

#[pyfunction]
fn convert_and_print_trace_witness(json: &PyString) {
    let trace_witness: TraceWitness<Fr> =
        serde_json::from_str(json.to_str().expect("PyString convertion failed."))
            .expect("Json deserialization to TraceWitness failed.");
    println!("{:?}", trace_witness);
}

#[pyfunction]
fn ast_to_halo2(json: &PyString) -> u128 {
    let uuid = chiquito_ast_to_halo2(json.to_str().expect("PyString convertion failed."));

    uuid
}

#[pyfunction]
fn halo2_mock_prover(witness_json: &PyString, ast_uuid: &PyLong) {
    chiquito_halo2_mock_prover(
        witness_json.to_str().expect("PyString convertion failed."),
        ast_uuid.extract().expect("PyLong convertion failed."),
    );
}

#[pymodule]
fn rust_chiquito(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(convert_and_print_ast, m)?)?;
    m.add_function(wrap_pyfunction!(convert_and_print_trace_witness, m)?)?;
    m.add_function(wrap_pyfunction!(ast_to_halo2, m)?)?;
    m.add_function(wrap_pyfunction!(halo2_mock_prover, m)?)?;
    Ok(())
}
