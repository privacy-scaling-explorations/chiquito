use crate::{
    field::Field,
    pil::{
        compiler::{compile, compile_super_circuits, PILColumn, PILExpr, PILQuery},
        ir::powdr_pil::PILCircuit,
    },
    sbpir::SBPIR,
    util::UUID,
    wit_gen::TraceWitness,
};
use std::{
    collections::HashMap,
    fmt::{Debug, Write},
};
extern crate regex;

#[allow(non_snake_case)]
/// User generate PIL code using this function. User needs to supply AST, TraceWitness, and a name
/// string for the circuit.
pub fn chiquito2Pil<F: Clone + Debug + Field, TraceArgs>(
    ast: SBPIR<F, TraceArgs>,
    witness: Option<TraceWitness<F>>,
    circuit_name: String,
) -> String {
    // generate PIL IR.
    let pil_ir = compile::<F, TraceArgs>(&ast, witness, circuit_name, &None);

    // generate Powdr PIL code.
    pil_ir_to_powdr_pil::<F>(pil_ir)
}

// Convert PIL IR to Powdr PIL code.
pub fn pil_ir_to_powdr_pil<F: Clone + Debug + Field>(pil_ir: PILCircuit<F>) -> String {
    let mut pil = String::new(); // The string to return.

    writeln!(
        pil,
        "// ===== START OF CIRCUIT: {} =====",
        pil_ir.circuit_name
    )
    .unwrap();

    // Namespace is equivalent to a circuit in PIL.
    writeln!(
        pil,
        "constant %NUM_STEPS_{} = {};",
        pil_ir.circuit_name.to_uppercase(),
        pil_ir.num_steps
    )
    .unwrap();
    writeln!(
        pil,
        "namespace {}(%NUM_STEPS_{});",
        pil_ir.circuit_name,
        pil_ir.circuit_name.to_uppercase()
    )
    .unwrap();

    // Declare witness columns in PIL.
    generate_pil_witness_columns(&mut pil, &pil_ir);

    // Declare fixed columns and their assignments in PIL.
    generate_pil_fixed_columns(&mut pil, &pil_ir);

    // generate constraints
    for expr in pil_ir.constraints {
        // recursively convert expressions to PIL strings
        let expr_string = convert_to_pil_expr_string(expr.clone());
        // each constraint is in the format of `constraint = 0`
        writeln!(pil, "{} = 0;", expr_string).unwrap();
    }

    // generate lookups
    for lookup in pil_ir.lookups {
        let (selector, src_dest_tuples) = lookup;
        let lookup_selector = selector.annotation();
        let mut lookup_source: Vec<String> = Vec::new();
        let mut lookup_destination: Vec<String> = Vec::new();
        for (src, dest) in src_dest_tuples {
            lookup_source.push(src.annotation());
            lookup_destination.push(dest.annotation());
        }
        // PIL lookups have the format of `selector { src1, src2, ... srcn } in {dest1, dest2, ...,
        // destn}`.
        writeln!(
            pil,
            "{} {{{}}} in {{{}}} ",
            lookup_selector,
            lookup_source.join(", "),
            lookup_destination.join(", ")
        )
        .unwrap();
    }

    writeln!(
        pil,
        "// ===== END OF CIRCUIT: {} =====",
        pil_ir.circuit_name
    )
    .unwrap();
    writeln!(pil).unwrap(); // Separator row for the circuit.

    pil
}

#[allow(non_snake_case)]
/// User generate PIL code for super circuit using this function.
/// User needs to supply a Vec<String> for `circuit_names`, the order of which should be the same as
/// the order of calling `sub_circuit()` function.
pub fn chiquitoSuperCircuit2Pil<F: Debug + Field, MappingArgs, TraceArgs>(
    super_asts: Vec<SBPIR<F, TraceArgs>>,
    super_trace_witnesses: HashMap<UUID, TraceWitness<F>>,
    ast_id_to_ir_id_mapping: HashMap<UUID, UUID>,
    circuit_names: Vec<String>,
) -> String {
    let mut pil = String::new(); // The string to return.

    // Generate PIL IRs for each sub circuit in the super circuit.
    let pil_irs = compile_super_circuits(
        super_asts,
        super_trace_witnesses,
        ast_id_to_ir_id_mapping,
        circuit_names,
    );

    // Generate Powdr PIL code for each sub circuit.
    for pil_ir in pil_irs {
        let pil_circuit = pil_ir_to_powdr_pil(pil_ir);
        writeln!(pil, "{}", pil_circuit).unwrap();
    }

    pil
}

fn generate_pil_witness_columns<F>(pil: &mut String, pil_ir: &PILCircuit<F>) {
    if !pil_ir.col_witness.is_empty() {
        writeln!(pil, "// === Witness Columns ===").unwrap();
        let mut col_witness = String::from("col witness ");

        let mut col_witness_vars = pil_ir
            .col_witness
            .iter()
            .map(|col| match col {
                PILColumn::Advice(_, annotation) => annotation.clone(),
                _ => panic!("Witness column should be an advice column."),
            })
            .collect::<Vec<String>>();

        // Get unique witness column annotations
        col_witness_vars.sort();
        col_witness_vars.dedup();
        col_witness = col_witness + col_witness_vars.join(", ").as_str() + ";";
        writeln!(pil, "{}", col_witness).unwrap();
    }
}

fn generate_pil_fixed_columns<F: Debug>(pil: &mut String, pil_ir: &PILCircuit<F>) {
    if !pil_ir.col_fixed.is_empty() {
        writeln!(
            pil,
            "// === Fixed Columns for Signals and Step Type Selectors ==="
        )
        .unwrap();
        for (col, assignments) in pil_ir.col_fixed.iter() {
            let fixed_name = match col {
                PILColumn::Fixed(_, annotation) => annotation.clone(),
                _ => panic!("Fixed column should be an advice or fixed column."),
            };
            let mut assignments_string = String::new();
            let assignments_vec = assignments
                .iter()
                .map(|assignment| format!("{:?}", assignment))
                .collect::<Vec<String>>();
            write!(
                assignments_string,
                "{}",
                assignments_vec.join(", ").as_str()
            )
            .unwrap();
            writeln!(pil, "col fixed {} = [{}];", fixed_name, assignments_string).unwrap();
        }
    }
}

// Convert PIL expression to Powdr PIL string recursively.
fn convert_to_pil_expr_string<F: Debug + Clone>(expr: PILExpr<F, PILQuery>) -> String {
    match expr {
        PILExpr::Const(constant) => format!("{:?}", constant),
        PILExpr::Sum(sum) => {
            let mut expr_string = String::new();
            for (index, expr) in sum.iter().enumerate() {
                expr_string += convert_to_pil_expr_string(expr.clone()).as_str();
                if index != sum.len() - 1 {
                    expr_string += " + ";
                }
            }
            format!("({})", expr_string)
        }
        PILExpr::Mul(mul) => {
            let mut expr_string = String::new();
            for (index, expr) in mul.iter().enumerate() {
                expr_string += convert_to_pil_expr_string(expr.clone()).as_str();
                if index != mul.len() - 1 {
                    expr_string += " * ";
                }
            }
            expr_string.to_string()
        }
        PILExpr::Neg(neg) => format!("(-{})", convert_to_pil_expr_string(*neg)),
        PILExpr::Pow(pow, power) => {
            format!("({})^{}", convert_to_pil_expr_string(*pow), power)
        }
        PILExpr::Query(queriable) => convert_to_pil_queriable_string(queriable),
    }
}

// Convert PIL query to Powdr PIL string recursively.
fn convert_to_pil_queriable_string(query: PILQuery) -> String {
    let (col, rot) = query;
    let annotation = col.annotation();
    if rot {
        format!("{}'", annotation)
    } else {
        annotation
    }
}
