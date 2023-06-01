use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
        VirtualCells,
    },
    poly::Rotation,
};

use crate::{
    ast::{query::Queriable, ForwardSignal, InternalSignal, StepType, ToField},
    compiler::{
        cell_manager::Placement, step_selector::StepSelector, FixedGenContext, TraceContext,
        WitnessGenContext,
    },
    dsl::StepTypeHandler,
    ir::{
        Circuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr,
    },
};

use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit};
use mock::test_ctx::TestContext;
use num_bigint::BigUint;
use polyexen::{
    analyze::{bound_base, find_bounds_poly, Analysis},
    expr::ExprDisplay,
    plaf::{
        backends::halo2::PlafH2Circuit,
        frontends::halo2::{gen_witness, get_plaf},
        Cell, CellDisplay, Plaf, PlafDisplayBaseTOML, PlafDisplayFixedCSV, VarDisplay,
    },
};
use std::fmt;
use zkevm_circuits::{
    bytecode_circuit::circuit::BytecodeCircuit,
    copy_circuit::CopyCircuit,
    evm_circuit::EvmCircuit,
    exp_circuit::ExpCircuit,
    keccak_circuit::KeccakCircuit,
    pi_circuit::PiCircuit,
    state_circuit::StateCircuit,
    super_circuit::SuperCircuit,
    tx_circuit::TxCircuit,
    util::SubCircuit,
    witness::{block_convert, Block},
};

use std::{
    fs::File,
    io::{self, Write},
};

use demo::utils::{alias_replace, gen_empty_block, name_challanges};

fn write_files(name: &str, plaf: &Plaf) -> Result<(), io::Error> {
    let mut base_file = File::create(format!("out/{}.toml", name))?;
    let mut fixed_file = File::create(format!("out/{}_fixed.csv", name))?;
    write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
    write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
    Ok(())
}

fn gen_circuit_plaf<C: Circuit<Fr> + SubCircuit<Fr>>(name: &str, k: u32, block: &Block<Fr>) {
    let circuit = C::new_from_block(&block);
    let mut plaf = get_plaf(k, &circuit).unwrap();
    name_challanges(&mut plaf);
    alias_replace(&mut plaf);
    write_files(name, &plaf).unwrap();
}
