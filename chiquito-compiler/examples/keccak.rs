use chiquito::{
    frontend::dsl::{lb::LookupTable, super_circuit, CircuitContext, StepTypeWGHandler},
    plonkish::{
        backend::halo2::{chiquitoSuperCircuit2Halo2, ChiquitoHalo2SuperCircuit},
        compiler::{
            cell_manager::{MaxWidthCellManager, SingleRowCellManager},
            config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::sc::SuperCircuit,
    },
    poly::ToExpr,
    sbpir::query::Queriable,
};
use std::{hash::Hash, ops::Neg};

use halo2_proofs::{
    dev::MockProver,
    halo2curves::{bn256::Fr, group::ff::PrimeField},
};

use std::{
    fs::File,
    io::{self, Write},
};

const BIT_COUNT: u64 = 3;
const PART_SIZE: u64 = 5;
const NUM_BYTES_PER_WORD: u64 = 8;
const NUM_BITS_PER_BYTE: u64 = 8;
const NUM_WORDS_TO_ABSORB: u64 = 17;
const RATE: u64 = NUM_WORDS_TO_ABSORB * NUM_BYTES_PER_WORD;
const NUM_BITS_PER_WORD: u64 = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE;
const NUM_PER_WORD: u64 = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE / 2;
const RATE_IN_BITS: u64 = RATE * NUM_BITS_PER_BYTE;
const NUM_ROUNDS: u64 = 24;
const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

const NUM_PER_WORD_BATCH3: u64 = 22;
const NUM_PER_WORD_BATCH4: u64 = 16;

const SQUEEZE_VECTOR_NUM: u64 = 4;
const SQUEEZE_SPLIT_NUM: u64 = 16;

const PART_SIZE_SQURE: u64 = PART_SIZE * PART_SIZE;

pub const ROUND_CST: [u64; NUM_ROUNDS as usize + 1] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
    0x0000000000000000,
];

pub const XOR_VALUE_BATCH2: [u64; 36] = [
    0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x8,
    0x9, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9,
];

pub const XOR_VALUE_BATCH3: [u64; 64] = [
    0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x40, 0x41,
    0x40, 0x41, 0x48, 0x49, 0x48, 0x49, 0x40, 0x41, 0x40, 0x41, 0x48, 0x49, 0x48, 0x49, 0x0, 0x1,
    0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x40, 0x41, 0x40, 0x41,
    0x48, 0x49, 0x48, 0x49, 0x40, 0x41, 0x40, 0x41, 0x48, 0x49, 0x48, 0x49,
];

pub const XOR_VALUE_BATCH4: [u64; 81] = [
    0x0, 0x1, 0x0, 0x8, 0x9, 0x8, 0x0, 0x1, 0x0, 0x40, 0x41, 0x40, 0x48, 0x49, 0x48, 0x40, 0x41,
    0x40, 0x0, 0x1, 0x0, 0x8, 0x9, 0x8, 0x0, 0x1, 0x0, 0x200, 0x201, 0x200, 0x208, 0x209, 0x208,
    0x200, 0x201, 0x200, 0x240, 0x241, 0x240, 0x248, 0x249, 0x248, 0x240, 0x241, 0x240, 0x200,
    0x201, 0x200, 0x208, 0x209, 0x208, 0x200, 0x201, 0x200, 0x0, 0x1, 0x0, 0x8, 0x9, 0x8, 0x0, 0x1,
    0x0, 0x40, 0x41, 0x40, 0x48, 0x49, 0x48, 0x40, 0x41, 0x40, 0x0, 0x1, 0x0, 0x8, 0x9, 0x8, 0x0,
    0x1, 0x0,
];

pub const CHI_VALUE: [u64; 125] = [
    0x0, 0x1, 0x1, 0x0, 0x0, 0x8, 0x9, 0x9, 0x8, 0x8, 0x8, 0x9, 0x9, 0x8, 0x8, 0x0, 0x1, 0x1, 0x0,
    0x0, 0x0, 0x1, 0x1, 0x0, 0x0, 0x40, 0x41, 0x41, 0x40, 0x40, 0x48, 0x49, 0x49, 0x48, 0x48, 0x48,
    0x49, 0x49, 0x48, 0x48, 0x40, 0x41, 0x41, 0x40, 0x40, 0x40, 0x41, 0x41, 0x40, 0x40, 0x40, 0x41,
    0x41, 0x40, 0x40, 0x48, 0x49, 0x49, 0x48, 0x48, 0x48, 0x49, 0x49, 0x48, 0x48, 0x40, 0x41, 0x41,
    0x40, 0x40, 0x40, 0x41, 0x41, 0x40, 0x40, 0x0, 0x1, 0x1, 0x0, 0x0, 0x8, 0x9, 0x9, 0x8, 0x8,
    0x8, 0x9, 0x9, 0x8, 0x8, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x1, 0x1, 0x0,
    0x0, 0x8, 0x9, 0x9, 0x8, 0x8, 0x8, 0x9, 0x9, 0x8, 0x8, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x1, 0x1,
    0x0, 0x0,
];

/// Pack bits in the range [0,BIT_SIZE[ into a sparse keccak word
fn pack<F: PrimeField>(bits: &[u8]) -> F {
    pack_with_base(bits, BIT_SIZE)
}

/// Pack bits in the range [0,BIT_SIZE[ into a sparse keccak word with the
/// specified bit base
fn pack_with_base<F: PrimeField>(bits: &[u8], base: usize) -> F {
    // \sum 8^i * bit_i
    let base = F::from(base as u64);
    bits.iter()
        .rev()
        .fold(F::ZERO, |acc, &bit| acc * base + F::from(bit as u64))
}

fn pack_u64<F: PrimeField>(value: u64) -> F {
    pack(
        &((0..NUM_BITS_PER_WORD)
            .map(|i| ((value >> i) & 1) as u8)
            .collect::<Vec<_>>()),
    )
}

/// Calculates a ^ b with a and b field elements
fn field_xor<F: PrimeField<Repr = [u8; 32]>>(a: F, b: F) -> F {
    let mut bytes = [0u8; 32];
    for (idx, (a, b)) in a
        .to_repr()
        .as_ref()
        .iter()
        .zip(b.to_repr().as_ref().iter())
        .enumerate()
    {
        bytes[idx] = *a ^ *b;
    }
    F::from_repr(bytes).unwrap()
}

fn convert_bytes_to_bits(bytes: Vec<u8>) -> Vec<u8> {
    bytes
        .iter()
        .map(|&byte| {
            let mut byte = byte;
            (0..8)
                .map(|_| {
                    let b = byte % 2;
                    byte /= 2;
                    b
                })
                .collect()
        })
        .collect::<Vec<Vec<u8>>>()
        .concat()
}

fn convert_field_to_vec_bits<F: PrimeField>(value: F) -> Vec<u8> {
    let mut v_vec = Vec::new();
    let mut left = 0;
    for (idx, &v1) in value.to_repr().as_ref().iter().enumerate() {
        if idx % 3 == 0 {
            v_vec.push(v1 % 8);
            v_vec.push((v1 / 8) % 8);
            left = v1 / 64;
        } else if idx % 3 == 1 {
            v_vec.push((v1 % 2) * 4 + left);
            v_vec.push((v1 / 2) % 8);
            v_vec.push((v1 / 16) % 8);
            left = v1 / 128;
        } else {
            v_vec.push((v1 % 4) * 2 + left);
            v_vec.push((v1 / 4) % 8);
            v_vec.push(v1 / 32);
            left = 0;
        }
    }
    v_vec[0..64].to_vec()
}

fn convert_bits_to_f<F: PrimeField<Repr = [u8; 32]>>(value_vec: &[u8]) -> F {
    assert_eq!(value_vec.len(), NUM_BITS_PER_WORD as usize);
    let mut sum_value_arr: Vec<u8> = (0..24)
        .map(|t| {
            if t % 3 == 0 {
                value_vec[(t / 3) * 8]
                    + value_vec[(t / 3) * 8 + 1] * 8
                    + (value_vec[(t / 3) * 8 + 2] % 4) * 64
            } else if t % 3 == 1 {
                value_vec[(t / 3) * 8 + 2] / 4
                    + value_vec[(t / 3) * 8 + 3] * 2
                    + (value_vec[(t / 3) * 8 + 4]) * 16
                    + ((value_vec[(t / 3) * 8 + 5]) % 2) * 128
            } else {
                value_vec[(t / 3) * 8 + 5] / 2
                    + value_vec[(t / 3) * 8 + 6] * 4
                    + (value_vec[(t / 3) * 8 + 7]) * 32
            }
        })
        .collect();
    while sum_value_arr.len() < 32 {
        sum_value_arr.push(0);
    }
    F::from_repr(sum_value_arr.try_into().unwrap()).unwrap()
}

fn eval_keccak_f_to_bit_vec4<F: PrimeField<Repr = [u8; 32]>>(value1: F, value2: F) -> Vec<(F, F)> {
    let v1_vec = convert_field_to_vec_bits(value1);
    let v2_vec = convert_field_to_vec_bits(value2);
    assert_eq!(v1_vec.len(), NUM_BITS_PER_WORD as usize);
    assert_eq!(v2_vec.len(), NUM_BITS_PER_WORD as usize);
    (0..NUM_PER_WORD_BATCH4 as usize)
        .map(|i| {
            (
                F::from_u128(
                    v1_vec[4 * i] as u128
                        + v1_vec[4 * i + 1] as u128 * 8
                        + v1_vec[4 * i + 2] as u128 * 64
                        + v1_vec[4 * i + 3] as u128 * 512,
                ),
                F::from_u128(
                    v2_vec[4 * i] as u128
                        + v2_vec[4 * i + 1] as u128 * 8
                        + v2_vec[4 * i + 2] as u128 * 64
                        + v2_vec[4 * i + 3] as u128 * 512,
                ),
            )
        })
        .collect()
}

fn keccak_xor_table_batch2<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_xor_row: Queriable<F> = ctx.fixed("xor row(batch 2)");
    let lookup_xor_c: Queriable<F> = ctx.fixed("xor value(batch 2)");

    let constants_value = XOR_VALUE_BATCH2;
    assert_eq!(lens, constants_value.len());
    ctx.pragma_num_steps(lens);

    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(i, lookup_xor_row, F::from(((i / 6) * 8 + i % 6) as u64));
            ctx.assign(i, lookup_xor_c, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_xor_row).add(lookup_xor_c))
}

fn keccak_xor_table_batch3<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_xor_row: Queriable<F> = ctx.fixed("xor row(batch 3)");
    let lookup_xor_c: Queriable<F> = ctx.fixed("xor value(batch 3)");

    let constants_value = XOR_VALUE_BATCH3;
    assert_eq!(lens, constants_value.len());
    ctx.pragma_num_steps(lens);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(
                i,
                lookup_xor_row,
                F::from(((i / 16) * 64 + (i % 16) / 4 * 8 + i % 4) as u64),
            );
            ctx.assign(i, lookup_xor_c, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_xor_row).add(lookup_xor_c))
}

fn keccak_xor_table_batch4<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_xor_row: Queriable<F> = ctx.fixed("xor row(batch 4)");
    let lookup_xor_c: Queriable<F> = ctx.fixed("xor value(batch 4)");

    let constants_value = XOR_VALUE_BATCH4;
    assert_eq!(lens, constants_value.len());
    ctx.pragma_num_steps(lens);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(
                i,
                lookup_xor_row,
                F::from((i / 27 * 512 + (i % 27) / 9 * 64 + (i % 9) / 3 * 8 + i % 3) as u64),
            );
            ctx.assign(i, lookup_xor_c, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_xor_row).add(lookup_xor_c))
}

fn keccak_chi_table<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_chi_row: Queriable<F> = ctx.fixed("chi row");
    let lookup_chi_c: Queriable<F> = ctx.fixed("chi value");

    let constants_value = CHI_VALUE;
    assert_eq!(lens, constants_value.len());
    ctx.pragma_num_steps(lens);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(
                i,
                lookup_chi_row,
                F::from(((i / 25) * 64 + (i % 25) / 5 * 8 + i % 5) as u64),
            );
            ctx.assign(i, lookup_chi_c, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_chi_row).add(lookup_chi_c))
}

fn keccak_pack_table<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_pack_row: Queriable<F> = ctx.fixed("pack row");
    let lookup_pack_c: Queriable<F> = ctx.fixed("pack value");
    ctx.pragma_num_steps((SQUEEZE_SPLIT_NUM * SQUEEZE_SPLIT_NUM) as usize);
    ctx.fixed_gen(move |ctx| {
        for i in 0..SQUEEZE_SPLIT_NUM as usize {
            let index = (i / 8) * 512 + (i % 8) / 4 * 64 + (i % 4) / 2 * 8 + i % 2;
            for j in 0..SQUEEZE_SPLIT_NUM as usize {
                let index_j = (j / 8) * 512 + (j % 8) / 4 * 64 + (j % 4) / 2 * 8 + j % 2;
                ctx.assign(
                    i * SQUEEZE_SPLIT_NUM as usize + j,
                    lookup_pack_row,
                    F::from((index * 4096 + index_j) as u64),
                );
                ctx.assign(
                    i * SQUEEZE_SPLIT_NUM as usize + j,
                    lookup_pack_c,
                    F::from((i * 16 + j) as u64),
                );
            }
        }
    });
    ctx.new_table(table().add(lookup_pack_row).add(lookup_pack_c))
}

fn keccak_round_constants_table<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_constant_row: Queriable<F> = ctx.fixed("constant row");
    let lookup_constant_c: Queriable<F> = ctx.fixed("constant value");

    let constants_value = ROUND_CST;
    ctx.pragma_num_steps(lens);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(i, lookup_constant_row, F::from(i as u64));
            ctx.assign(i, lookup_constant_c, pack_u64::<F>(value));
        }
    });
    ctx.new_table(table().add(lookup_constant_row).add(lookup_constant_c))
}

struct PreValues<F> {
    s_vec: Vec<F>,
    absorb_rows: Vec<F>,
    round_value: F,
    absorb_split_vec: Vec<Vec<F>>,
    absorb_split_input_vec: Vec<Vec<F>>,
    split_values: Vec<Vec<(F, F)>>,
    is_padding_vec: Vec<Vec<F>>,
    input_len: F,
    data_rlc_vec: Vec<Vec<F>>,
    data_rlc: F,
    input_acc: F,
    padded: F,
}

#[derive(Clone)]
struct SqueezeValues<F> {
    s_new_vec: Vec<F>,
    squeeze_split_vec: Vec<Vec<F>>,
    squeeze_split_output_vec: Vec<Vec<F>>,
    hash_rlc: F,
}

#[derive(Clone)]
struct OneRoundValues<F> {
    round: F,
    next_round: F,
    round_cst: F,
    input_len: F,
    input_acc: F,

    s_vec: Vec<F>,
    s_new_vec: Vec<F>,

    theta_split_vec: Vec<Vec<F>>,
    theta_split_xor_vec: Vec<Vec<F>>,
    theta_sum_split_vec: Vec<Vec<F>>,
    theta_sum_split_xor_vec: Vec<Vec<F>>,

    rho_bit_0: Vec<F>,
    rho_bit_1: Vec<F>,

    chi_split_value_vec: Vec<Vec<F>>,

    final_sum_split_vec: Vec<F>,
    final_xor_split_vec: Vec<F>,

    svalues: SqueezeValues<F>,
    data_rlc: F,
    padded: F,
}

fn eval_keccak_f_one_round<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    round: u64,
    cst: u64,
    s_vec: Vec<F>,
    input_len: u64,
    data_rlc: F,
    input_acc: F,
    padded: F,
) -> OneRoundValues<F> {
    let mut s_new_vec = Vec::new();
    let mut theta_split_vec = Vec::new();
    let mut theta_split_xor_vec = Vec::new();
    let mut theta_sum_split_xor_value_vec = Vec::new();
    let mut theta_sum_split_xor_move_value_vec = Vec::new();
    let mut theta_sum_split_vec = Vec::new();
    let mut theta_sum_split_xor_vec = Vec::new();
    let mut rho_pi_s_new_vec = vec![F::ZERO; PART_SIZE_SQURE as usize];
    let mut rho_bit_0 = vec![F::ZERO; 15];
    let mut rho_bit_1 = vec![F::ZERO; 15];
    let mut chi_sum_value_vec = Vec::new();
    let mut chi_sum_split_value_vec = Vec::new();
    let mut chi_split_value_vec = Vec::new();
    let mut final_sum_split_vec = Vec::new();
    let mut final_xor_split_vec = Vec::new();

    let mut t_vec = vec![0; PART_SIZE_SQURE as usize];
    {
        let mut i: usize = 1;
        let mut j: usize = 0;
        for t in 0..PART_SIZE_SQURE as usize {
            if t == 0 {
                i = 0;
                j = 0
            } else if t == 1 {
                i = 1;
                j = 0;
            } else {
                let m = j;
                j = (2 * i + 3 * j) % PART_SIZE as usize;
                i = m;
            }
            t_vec[i * PART_SIZE as usize + j] = t;
        }
    }

    for i in 0..PART_SIZE as usize {
        let sum = s_vec[i * PART_SIZE as usize]
            + s_vec[i * PART_SIZE as usize + 1]
            + s_vec[i * PART_SIZE as usize + 2]
            + s_vec[i * PART_SIZE as usize + 3]
            + s_vec[i * PART_SIZE as usize + 4];
        let sum_bits = convert_field_to_vec_bits(sum);

        let xor: F = field_xor(
            field_xor(
                field_xor(
                    field_xor(
                        s_vec[i * PART_SIZE as usize],
                        s_vec[i * PART_SIZE as usize + 1],
                    ),
                    s_vec[i * PART_SIZE as usize + 2],
                ),
                s_vec[i * PART_SIZE as usize + 3],
            ),
            s_vec[i * PART_SIZE as usize + 4],
        );
        let xor_bits = convert_field_to_vec_bits(xor);
        let mut xor_bits_move = xor_bits.clone();
        xor_bits_move.rotate_right(1);
        let xor_rot: F = convert_bits_to_f(&xor_bits_move);

        let mut sum_split = Vec::new();
        let mut sum_split_xor = Vec::new();
        for k in 0..sum_bits.len() / 2 {
            if k == sum_bits.len() / 2 - 1 {
                sum_split.push(F::from_u128(sum_bits[2 * k] as u128));
                sum_split.push(F::from_u128(sum_bits[2 * k + 1] as u128));
                sum_split_xor.push(F::from_u128(xor_bits[2 * k] as u128));
                sum_split_xor.push(F::from_u128(xor_bits[2 * k + 1] as u128));
            } else {
                sum_split.push(
                    F::from_u128(sum_bits[2 * k] as u128)
                        + F::from_u128(sum_bits[2 * k + 1] as u128) * F::from_u128(8),
                );
                sum_split_xor.push(
                    F::from_u128(xor_bits[2 * k] as u128)
                        + F::from_u128(xor_bits[2 * k + 1] as u128) * F::from_u128(8),
                );
            }
        }

        theta_split_vec.push(sum_split);
        theta_split_xor_vec.push(sum_split_xor);
        theta_sum_split_xor_value_vec.push(xor);
        theta_sum_split_xor_move_value_vec.push(xor_rot);
    }

    let mut rho_index = 0;
    for i in 0..PART_SIZE as usize {
        let xor = theta_sum_split_xor_value_vec[(i + PART_SIZE as usize - 1) % PART_SIZE as usize];
        let xor_rot = theta_sum_split_xor_move_value_vec[(i + 1) % PART_SIZE as usize];
        for j in 0..PART_SIZE as usize {
            let v = ((t_vec[i * PART_SIZE as usize + j] + 1) * t_vec[i * PART_SIZE as usize + j]
                / 2)
                % NUM_BITS_PER_WORD as usize;
            let st = s_vec[i * PART_SIZE as usize + j] + xor + xor_rot;
            let st_xor = field_xor(field_xor(s_vec[i * PART_SIZE as usize + j], xor), xor_rot);
            let mut st_split = Vec::new();
            let mut st_split_xor = Vec::new();
            let mut st_bit_vec = convert_field_to_vec_bits(st);
            let mut st_bit_xor_vec = convert_field_to_vec_bits(st_xor);

            // rho
            // a[x][y][z] = a[x][y][z-(t+1)(t+2)/2]
            if v % 3 == 1 {
                rho_bit_0[rho_index] =
                    F::from(st_bit_vec[1] as u64) * F::from_u128(8) + F::from(st_bit_vec[0] as u64);
                rho_bit_1[rho_index] = F::from(st_bit_vec[NUM_BITS_PER_WORD as usize - 1] as u64);
                rho_index += 1
            } else if v % 3 == 2 {
                rho_bit_0[rho_index] = F::from(st_bit_vec[0] as u64);
                rho_bit_1[rho_index] = F::from(st_bit_vec[NUM_BITS_PER_WORD as usize - 1] as u64)
                    * F::from_u128(8)
                    + F::from(st_bit_vec[NUM_BITS_PER_WORD as usize - 2] as u64);
                rho_index += 1
            }

            st_bit_vec.rotate_right(v);
            st_bit_xor_vec.rotate_right(v);

            for i in 0..st_bit_vec.len() / 3 {
                st_split.push(
                    F::from_u128(st_bit_vec[3 * i] as u128)
                        + F::from_u128(st_bit_vec[3 * i + 1] as u128) * F::from_u128(8)
                        + F::from_u128(st_bit_vec[3 * i + 2] as u128) * F::from_u128(64),
                );
                st_split_xor.push(
                    F::from_u128(st_bit_xor_vec[3 * i] as u128)
                        + F::from_u128(st_bit_xor_vec[3 * i + 1] as u128) * F::from_u128(8)
                        + F::from_u128(st_bit_xor_vec[3 * i + 2] as u128) * F::from_u128(64),
                );
            }
            st_split.push(F::from_u128(
                st_bit_vec[NUM_BITS_PER_WORD as usize - 1] as u128,
            ));
            st_split_xor.push(F::from_u128(
                st_bit_xor_vec[NUM_BITS_PER_WORD as usize - 1] as u128,
            ));

            theta_sum_split_vec.push(st_split);
            theta_sum_split_xor_vec.push(st_split_xor);

            // pi
            // a[y][2x + 3y] = a[x][y]
            rho_pi_s_new_vec[j * PART_SIZE as usize + ((2 * i + 3 * j) % PART_SIZE as usize)] =
                convert_bits_to_f(&st_bit_xor_vec);
        }
    }

    // chi
    // a[x] = a[x] ^ (~a[x+1] & a[x+2])
    for i in 0..PART_SIZE as usize {
        for j in 0..PART_SIZE as usize {
            let a_vec = convert_field_to_vec_bits(rho_pi_s_new_vec[i * PART_SIZE as usize + j]);
            let b_vec =
                convert_field_to_vec_bits(rho_pi_s_new_vec[((i + 1) % 5) * PART_SIZE as usize + j]);
            let c_vec =
                convert_field_to_vec_bits(rho_pi_s_new_vec[((i + 2) % 5) * PART_SIZE as usize + j]);
            let sum_vec: Vec<u8> = a_vec
                .iter()
                .zip(b_vec.iter().zip(c_vec.iter()))
                .map(|(&a, (&b, &c))| 3 + b - 2 * a - c)
                .collect();
            let sum: F = convert_bits_to_f(&sum_vec);

            let split_chi_value: Vec<u8> = sum_vec
                .iter()
                .map(|&v| if v == 1 || v == 2 { 1 } else { 0 })
                .collect();
            let sum_chi = convert_bits_to_f(&split_chi_value);

            let sum_split_vec: Vec<F> = (0..NUM_PER_WORD_BATCH3 as usize)
                .map(|i| {
                    if i == NUM_PER_WORD_BATCH3 as usize - 1 {
                        F::from_u128(sum_vec[3 * i] as u128)
                    } else {
                        F::from_u128(
                            sum_vec[3 * i] as u128
                                + sum_vec[3 * i + 1] as u128 * 8
                                + sum_vec[3 * i + 2] as u128 * 64,
                        )
                    }
                })
                .collect();
            let chi_split_vec: Vec<F> = (0..NUM_PER_WORD_BATCH3 as usize)
                .map(|i| {
                    if i == NUM_PER_WORD_BATCH3 as usize - 1 {
                        F::from_u128(split_chi_value[3 * i] as u128)
                    } else {
                        F::from_u128(
                            split_chi_value[3 * i] as u128
                                + split_chi_value[3 * i + 1] as u128 * 8
                                + split_chi_value[3 * i + 2] as u128 * 64,
                        )
                    }
                })
                .collect();

            chi_sum_value_vec.push(sum);
            s_new_vec.push(sum_chi);
            chi_sum_split_value_vec.push(sum_split_vec);
            chi_split_value_vec.push(chi_split_vec);
        }
    }

    let s_iota_vec = convert_field_to_vec_bits(s_new_vec[0]);
    let cst_vec = convert_field_to_vec_bits(pack_u64::<F>(cst));
    let split_xor_vec: Vec<u8> = s_iota_vec
        .iter()
        .zip(cst_vec.iter())
        .map(|(v1, v2)| v1 ^ v2)
        .collect();
    let xor_rows: Vec<(F, F)> = s_iota_vec
        .iter()
        .zip(cst_vec.iter())
        .map(|(v1, v2)| {
            (
                F::from_u128((v1 + v2) as u128),
                F::from_u128((v1 ^ v2) as u128),
            )
        })
        .collect();

    for i in 0..NUM_PER_WORD_BATCH4 as usize {
        final_sum_split_vec.push(
            xor_rows[4 * i].0
                + xor_rows[4 * i + 1].0 * F::from_u128(8)
                + xor_rows[4 * i + 2].0 * F::from_u128(64)
                + xor_rows[4 * i + 3].0 * F::from_u128(512),
        );
        final_xor_split_vec.push(
            xor_rows[4 * i].1
                + xor_rows[4 * i + 1].1 * F::from_u128(8)
                + xor_rows[4 * i + 2].1 * F::from_u128(64)
                + xor_rows[4 * i + 3].1 * F::from_u128(512),
        );
    }

    s_new_vec[0] = convert_bits_to_f(&split_xor_vec);

    let svalues = SqueezeValues {
        s_new_vec: Vec::new(),
        squeeze_split_vec: Vec::new(),
        squeeze_split_output_vec: Vec::new(),
        hash_rlc: F::ZERO,
    };

    let next_round = if round < NUM_ROUNDS - 1 { round + 1 } else { 0 };

    OneRoundValues {
        round: F::from(round),
        round_cst: pack_u64::<F>(cst),
        input_len: F::from(input_len),
        next_round: F::from(next_round),

        s_vec,
        s_new_vec,

        theta_split_vec,
        theta_split_xor_vec,
        theta_sum_split_vec,
        theta_sum_split_xor_vec,

        rho_bit_0,
        rho_bit_1,

        chi_split_value_vec,

        final_sum_split_vec,
        final_xor_split_vec,

        svalues,
        data_rlc,
        input_acc,
        padded,
    }
}

fn keccak_circuit<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    ctx: &mut CircuitContext<F, KeccakCircuit>,
    param: CircuitParams,
) {
    use chiquito::frontend::dsl::cb::*;

    let s_vec: Vec<Queriable<F>> = (0..PART_SIZE_SQURE)
        .map(|i| ctx.forward(&format!("s[{}][{}]", i / PART_SIZE, i % PART_SIZE)))
        .collect();

    let round = ctx.forward("round");
    let data_rlc = ctx.forward("data_rlc");

    let input_len = ctx.forward("input_len");
    let input_acc = ctx.forward("input_acc");

    let padded = ctx.forward("padded");

    let keccak_first_step = ctx.step_type_def("keccak first step", |ctx| {
        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        let absorb_vec: Vec<Queriable<F>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| ctx.internal(&format!("absorb_{}", i)))
            .collect();
        let setup_absorb_vec = absorb_vec.clone();

        let absorb_split_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("absorb_split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_absorb_split_vec = absorb_split_vec.clone();

        let absorb_split_input_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("absorb_split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_absorb_split_input_vec = absorb_split_input_vec.clone();

        let is_padding_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("is_padding_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_is_padding_vec = is_padding_vec.clone();

        let data_rlc_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("is_padding_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_data_rlc_vec = data_rlc_vec.clone();

        ctx.setup(move |ctx| {
            for i in 0..PART_SIZE as usize {
                for j in 0..PART_SIZE as usize {
                    ctx.constr(eq(setup_s_vec[i * PART_SIZE as usize + j], 0));
                    if j * PART_SIZE as usize + i < NUM_WORDS_TO_ABSORB as usize {
                        // xor
                        // 000 xor 000/001 -> 000 + 000/001
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE as usize + j]
                                + setup_absorb_vec[j * PART_SIZE as usize + i],
                            setup_s_vec[i * PART_SIZE as usize + j].next(),
                        ));

                        let mut tmp_absorb_split_sum_vec = setup_absorb_split_vec
                            [j * PART_SIZE as usize + i][SQUEEZE_SPLIT_NUM as usize / 2 - 1]
                            * 1;
                        for k in 1..SQUEEZE_SPLIT_NUM as usize / 2 {
                            tmp_absorb_split_sum_vec = tmp_absorb_split_sum_vec * 4096 * 4096
                                + setup_absorb_split_vec[j * PART_SIZE as usize + i]
                                    [SQUEEZE_SPLIT_NUM as usize / 2 - k - 1];
                        }
                        ctx.constr(eq(
                            setup_absorb_vec[j * PART_SIZE as usize + i],
                            tmp_absorb_split_sum_vec,
                        ));

                        for k in 0..SQUEEZE_SPLIT_NUM as usize / 2 {
                            ctx.add_lookup(
                                param
                                    .pack_table
                                    .apply(setup_absorb_split_vec[j * PART_SIZE as usize + i][k])
                                    .apply(
                                        setup_absorb_split_input_vec[j * PART_SIZE as usize + i][k],
                                    ),
                            );
                            ctx.constr(eq(
                                (setup_is_padding_vec[j * PART_SIZE as usize + i][k] - 1)
                                    * setup_is_padding_vec[j * PART_SIZE as usize + i][k],
                                0,
                            ));
                        }
                    } else {
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE as usize + j],
                            setup_s_vec[i * PART_SIZE as usize + j].next(),
                        ));
                    }
                }
            }
            ctx.constr(eq(data_rlc, 0));
            ctx.transition(eq(
                setup_data_rlc_vec[NUM_WORDS_TO_ABSORB as usize - 1]
                    [SQUEEZE_SPLIT_NUM as usize / 2 - 1],
                data_rlc.next(),
            ));
            let mut acc_value = 0.expr() * 1;
            for i in 0..NUM_WORDS_TO_ABSORB as usize {
                if i == 0 {
                    // data_rlc_vec[0][0] = 0 * 256 + absorb_split_input_vec[0][0];
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][0],
                        (data_rlc * 256 + setup_absorb_split_input_vec[i][0])
                            * (1.expr() - setup_is_padding_vec[i][0])
                            + data_rlc * setup_is_padding_vec[i][0],
                    ));
                } else {
                    // data_rlc_vec[0][0] = 0 * 256 + absorb_split_input_vec[0][0];
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][0],
                        (setup_data_rlc_vec[i - 1][SQUEEZE_SPLIT_NUM as usize / 2 - 1] * 256
                            + setup_absorb_split_input_vec[i][0])
                            * (setup_is_padding_vec[i][0] - 1).neg()
                            + setup_data_rlc_vec[i - 1][SQUEEZE_SPLIT_NUM as usize / 2 - 1]
                                * setup_is_padding_vec[i][0],
                    ));
                }

                for k in 1..SQUEEZE_SPLIT_NUM as usize / 2 {
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][k],
                        (setup_data_rlc_vec[i][k - 1] * 256 + setup_absorb_split_input_vec[i][k])
                            * (setup_is_padding_vec[i][k] - 1).neg()
                            + setup_data_rlc_vec[i][k - 1] * setup_is_padding_vec[i][k],
                    ));
                }
                acc_value = acc_value + (1.expr() - setup_is_padding_vec[i][0]);
                if i == 0 {
                    ctx.constr(eq(setup_is_padding_vec[i][0], 0));
                } else {
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7])
                            * ((setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7]) - 1),
                        0,
                    ));
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7])
                            * (setup_absorb_split_vec[i][0] - 1),
                        0,
                    ));
                }
                for k in 1..8 {
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                            * ((setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1]) - 1),
                        0,
                    ));
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                            * (setup_absorb_split_vec[i][k] - 1),
                        0,
                    ));
                    // the last one
                    if k == 7 && i == NUM_WORDS_TO_ABSORB as usize - 1 {
                        // the padding length is equal than 1 byte
                        ctx.constr(eq(
                            (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                                * (setup_absorb_split_vec[i][k] - 2097153),
                            0,
                        ));
                        // the padding length is bigger than 1 byte
                        ctx.constr(eq(
                            setup_is_padding_vec[i][k - 1]
                                * (setup_absorb_split_vec[i][k] - 2097152),
                            0,
                        ));
                    } else {
                        ctx.constr(eq(
                            (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                                * (setup_absorb_split_vec[i][k] - 1),
                            0,
                        ));
                        // the first padding byte = 1, other = 0
                        ctx.constr(eq(
                            setup_is_padding_vec[i][k]
                                * (setup_is_padding_vec[i][k]
                                    - setup_is_padding_vec[i][k - 1]
                                    - setup_absorb_split_vec[i][k]),
                            0,
                        ));
                    }

                    acc_value = acc_value + (1.expr() - setup_is_padding_vec[i][k]);
                }
            }
            ctx.constr(eq(
                (input_len - input_acc - acc_value.clone())
                    * setup_is_padding_vec[NUM_WORDS_TO_ABSORB as usize - 1][7],
                0,
            ));
            ctx.transition(eq(input_acc + acc_value, input_acc.next()));

            ctx.constr(eq(round, 0));
            ctx.transition(eq(round, round.next()));
            ctx.transition(eq(input_len, input_len.next()));
            ctx.constr(eq(padded, 0));
            ctx.transition(eq(
                setup_is_padding_vec[NUM_WORDS_TO_ABSORB as usize - 1][7],
                padded.next(),
            ));
        });

        ctx.wg::<PreValues<F>, _>(move |ctx, values| {
            for (q, v) in absorb_vec.iter().zip(values.absorb_rows.iter()) {
                ctx.assign(*q, *v)
            }

            for i in 0..PART_SIZE as usize {
                for j in 0..PART_SIZE as usize {
                    ctx.assign(s_vec[i * PART_SIZE as usize + j], F::ZERO);
                }
            }
            for (q_vec, v_vec) in absorb_split_vec.iter().zip(values.absorb_split_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }
            for (q_vec, v_vec) in absorb_split_input_vec
                .iter()
                .zip(values.absorb_split_input_vec.iter())
            {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for (q_vec, v_vec) in is_padding_vec.iter().zip(values.is_padding_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for (q_vec, v_vec) in data_rlc_vec.iter().zip(values.data_rlc_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }
            ctx.assign(round, values.round_value);
            ctx.assign(input_len, values.input_len);
            ctx.assign(data_rlc, values.data_rlc);
            ctx.assign(input_acc, values.input_acc);
            ctx.assign(padded, values.padded);
        })
    });

    let keccak_pre_step = ctx.step_type_def("keccak pre step", |ctx| {
        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        let absorb_vec: Vec<Queriable<F>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| ctx.internal(&format!("absorb_{}", i)))
            .collect();
        let setup_absorb_vec = absorb_vec.clone();

        let absorb_split_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("absorb_split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_absorb_split_vec = absorb_split_vec.clone();

        let absorb_split_input_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("absorb_split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_absorb_split_input_vec = absorb_split_input_vec.clone();

        let sum_split_value_vec: Vec<Queriable<F>> = (0..PART_SIZE_SQURE)
            .map(|i| ctx.internal(&format!("sum_split_value_{}", i)))
            .collect();
        let setup_sum_split_value_vec = sum_split_value_vec.clone();

        let split_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..NUM_PER_WORD_BATCH4)
                    .map(|j| ctx.internal(&format!("split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_split_vec = split_vec.clone();

        let split_xor_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..NUM_PER_WORD_BATCH4)
                    .map(|j| ctx.internal(&format!("split_xor_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_split_xor_vec = split_xor_vec.clone();

        let is_padding_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("is_padding_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_is_padding_vec = is_padding_vec.clone();

        let data_rlc_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..8)
                    .map(|j| ctx.internal(&format!("data_rlc_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_data_rlc_vec = data_rlc_vec.clone();

        ctx.setup(move |ctx| {
            for i in 0..PART_SIZE as usize {
                for j in 0..PART_SIZE as usize {
                    if j * PART_SIZE as usize + i < NUM_WORDS_TO_ABSORB as usize {
                        // xor
                        ctx.constr(eq(
                            setup_s_vec[i * PART_SIZE as usize + j]
                                + setup_absorb_vec[j * PART_SIZE as usize + i],
                            setup_sum_split_value_vec[i * PART_SIZE as usize + j],
                        ));

                        let mut tmp_absorb_split_sum_vec = setup_absorb_split_vec
                            [j * PART_SIZE as usize + i][SQUEEZE_SPLIT_NUM as usize / 2 - 1]
                            * 1;
                        for k in 1..SQUEEZE_SPLIT_NUM as usize / 2 {
                            tmp_absorb_split_sum_vec = tmp_absorb_split_sum_vec * 4096 * 4096
                                + setup_absorb_split_vec[j * PART_SIZE as usize + i]
                                    [SQUEEZE_SPLIT_NUM as usize / 2 - k - 1];
                        }
                        ctx.constr(eq(
                            setup_absorb_vec[j * PART_SIZE as usize + i],
                            tmp_absorb_split_sum_vec,
                        ));
                        for k in 0..SQUEEZE_SPLIT_NUM as usize / 2 {
                            ctx.add_lookup(
                                param
                                    .pack_table
                                    .apply(setup_absorb_split_vec[j * PART_SIZE as usize + i][k])
                                    .apply(
                                        setup_absorb_split_input_vec[j * PART_SIZE as usize + i][k],
                                    ),
                            );
                        }

                        for k in 0..NUM_PER_WORD_BATCH4 as usize {
                            ctx.add_lookup(
                                param
                                    .xor_table_batch4
                                    .apply(setup_split_vec[j * PART_SIZE as usize + i][k])
                                    .apply(setup_split_xor_vec[j * PART_SIZE as usize + i][k]),
                            );
                        }
                    } else {
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE as usize + j],
                            setup_s_vec[i * PART_SIZE as usize + j].next(),
                        ));
                    }
                }
            }

            ctx.transition(eq(
                setup_data_rlc_vec[NUM_WORDS_TO_ABSORB as usize - 1]
                    [SQUEEZE_SPLIT_NUM as usize / 2 - 1],
                data_rlc.next(),
            ));

            let mut acc_value = 0.expr() * 1;
            for i in 0..NUM_WORDS_TO_ABSORB as usize {
                if i == 0 {
                    // data_rlc_vec[0][0] = 0 * 256 + absorb_split_input_vec[0][0];
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][0],
                        (data_rlc * 256 + setup_absorb_split_input_vec[i][0])
                            * (setup_is_padding_vec[i][0] - 1).neg()
                            + data_rlc * setup_is_padding_vec[i][0],
                    ));
                } else {
                    // data_rlc_vec[0][0] = 0 * 256 + absorb_split_input_vec[0][0];
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][0],
                        (setup_data_rlc_vec[i - 1][SQUEEZE_SPLIT_NUM as usize / 2 - 1] * 256
                            + setup_absorb_split_input_vec[i][0])
                            * (setup_is_padding_vec[i][0] - 1).neg()
                            + setup_data_rlc_vec[i - 1][SQUEEZE_SPLIT_NUM as usize / 2 - 1]
                                * setup_is_padding_vec[i][0],
                    ));
                }
                for k in 1..SQUEEZE_SPLIT_NUM as usize / 2 {
                    ctx.constr(eq(
                        setup_data_rlc_vec[i][k],
                        (setup_data_rlc_vec[i][k - 1] * 256 + setup_absorb_split_input_vec[i][k])
                            * (setup_is_padding_vec[i][k] - 1).neg()
                            + setup_data_rlc_vec[i][k - 1] * setup_is_padding_vec[i][k],
                    ));
                }

                acc_value = acc_value + (1.expr() - setup_is_padding_vec[i][0]);
                if i == 0 {
                    ctx.constr(eq(
                        setup_is_padding_vec[i][0] * (setup_is_padding_vec[i][0] - 1),
                        0,
                    ));
                } else {
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7])
                            * ((setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7]) - 1),
                        0,
                    ));
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][0] - setup_is_padding_vec[i - 1][7])
                            * (setup_absorb_split_vec[i][0] - 1),
                        0,
                    ));
                }
                for k in 1..8 {
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                            * ((setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1]) - 1),
                        0,
                    ));
                    ctx.constr(eq(
                        (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                            * (setup_absorb_split_vec[i][k] - 1),
                        0,
                    ));

                    if k == 7 && i == NUM_WORDS_TO_ABSORB as usize - 1 {
                        ctx.constr(eq(
                            (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                                * (setup_absorb_split_vec[i][k] - 2097153),
                            0,
                        ));
                        ctx.constr(eq(
                            setup_is_padding_vec[i][k - 1]
                                * (setup_absorb_split_vec[i][k] - 2097152),
                            0,
                        ));
                    } else {
                        ctx.constr(eq(
                            (setup_is_padding_vec[i][k] - setup_is_padding_vec[i][k - 1])
                                * (setup_absorb_split_vec[i][k] - 1),
                            0,
                        ));
                        ctx.constr(eq(
                            setup_is_padding_vec[i][k]
                                * (setup_is_padding_vec[i][k]
                                    - setup_is_padding_vec[i][k - 1]
                                    - setup_absorb_split_vec[i][k]),
                            0,
                        ));
                    }
                    acc_value = acc_value + (1.expr() - setup_is_padding_vec[i][k]);
                }
            }

            for s in 0..NUM_WORDS_TO_ABSORB as usize {
                let mut sum_split_vec = setup_split_vec[s][NUM_PER_WORD_BATCH4 as usize - 1] * 1;
                let mut sum_split_xor_vec =
                    setup_split_xor_vec[s][NUM_PER_WORD_BATCH4 as usize - 1] * 1;
                for (&value, &xor_value) in setup_split_vec[s]
                    .iter()
                    .rev()
                    .zip(setup_split_xor_vec[s].iter().rev())
                    .skip(1)
                {
                    sum_split_vec = sum_split_vec * 64 * 64 + value;
                    sum_split_xor_vec = sum_split_xor_vec * 64 * 64 + xor_value;
                }
                ctx.constr(eq(
                    sum_split_vec,
                    setup_sum_split_value_vec
                        [(s % PART_SIZE as usize) * PART_SIZE as usize + s / PART_SIZE as usize],
                ));
                ctx.transition(eq(
                    sum_split_xor_vec,
                    setup_s_vec
                        [(s % PART_SIZE as usize) * PART_SIZE as usize + s / PART_SIZE as usize]
                        .next(),
                ));
            }

            ctx.constr(eq(
                (input_len - input_acc - acc_value.clone())
                    * setup_is_padding_vec[NUM_WORDS_TO_ABSORB as usize - 1][7],
                0,
            ));
            ctx.transition(eq(input_acc + acc_value, input_acc.next()));

            ctx.transition(eq(round, round.next()));
            ctx.transition(eq(input_len, input_len.next()));

            ctx.constr(eq(padded, 0));
            ctx.transition(eq(
                setup_is_padding_vec[NUM_WORDS_TO_ABSORB as usize - 1][7],
                padded.next(),
            ));
        });

        ctx.wg::<PreValues<F>, _>(move |ctx, values| {
            ctx.assign(round, F::ZERO);
            for (q, v) in absorb_vec.iter().zip(values.absorb_rows.iter()) {
                ctx.assign(*q, *v)
            }

            for i in 0..PART_SIZE as usize {
                for j in 0..PART_SIZE as usize {
                    ctx.assign(s_vec[i * PART_SIZE as usize + j], F::ZERO);
                }
            }
            for (q_vec, v_vec) in absorb_split_vec.iter().zip(values.absorb_split_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }
            for (q_vec, v_vec) in absorb_split_input_vec
                .iter()
                .zip(values.absorb_split_input_vec.iter())
            {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for (q_vec, v_vec) in is_padding_vec.iter().zip(values.is_padding_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for (q_vec, v_vec) in data_rlc_vec.iter().zip(values.data_rlc_vec.iter()) {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for i in 0..PART_SIZE as usize {
                for j in 0..PART_SIZE as usize {
                    if j * PART_SIZE as usize + i < NUM_WORDS_TO_ABSORB as usize {
                        ctx.assign(
                            sum_split_value_vec[i * PART_SIZE as usize + j],
                            values.s_vec[i * PART_SIZE as usize + j]
                                + values.absorb_rows[j * PART_SIZE as usize + i],
                        );
                        ctx.assign(
                            absorb_vec[j * PART_SIZE as usize + i],
                            values.absorb_rows[j * PART_SIZE as usize + i],
                        );
                    } else {
                        ctx.assign(
                            sum_split_value_vec[i * PART_SIZE as usize + j],
                            values.s_vec[i * PART_SIZE as usize + j],
                        );
                    }
                    ctx.assign(
                        s_vec[i * PART_SIZE as usize + j],
                        values.s_vec[i * PART_SIZE as usize + j],
                    );
                }
            }

            for i in 0..NUM_WORDS_TO_ABSORB as usize {
                for j in 0..NUM_PER_WORD_BATCH4 as usize {
                    ctx.assign(split_vec[i][j], values.split_values[i][j].0);
                    ctx.assign(split_xor_vec[i][j], values.split_values[i][j].1);
                }
            }
            ctx.assign(input_len, values.input_len);
            ctx.assign(data_rlc, values.data_rlc);
            ctx.assign(input_acc, values.input_acc);
            ctx.assign(padded, values.padded);
        })
    });

    let keccak_one_round_step_vec: Vec<StepTypeWGHandler<F, OneRoundValues<F>, _>> = (0..2)
        .map(|last| {
            ctx.step_type_def("keccak one round", |ctx| {
                let s_vec = s_vec.clone();
                let setup_s_vec = s_vec.clone();

                let theta_split_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE)
                    .map(|i| {
                        (0..NUM_PER_WORD + 1)
                            .map(|j| ctx.internal(&format!("theta_split_{}_{}", i, j)))
                            .collect()
                    })
                    .collect();
                let setup_theta_split_vec = theta_split_vec.clone();

                let theta_split_xor_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE)
                    .map(|i| {
                        (0..NUM_PER_WORD + 1)
                            .map(|j| ctx.internal(&format!("theta_split_xor_{}_{}", i, j)))
                            .collect()
                    })
                    .collect();
                let setup_theta_split_xor_vec = theta_split_xor_vec.clone();

                let theta_sum_split_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE_SQURE)
                    .map(|i| {
                        (0..NUM_PER_WORD_BATCH3)
                            .map(|j| ctx.internal(&format!("theta_sum_split_{}_{}", i, j)))
                            .collect()
                    })
                    .collect();
                let setup_theta_sum_split_vec = theta_sum_split_vec.clone();

                let theta_sum_split_xor_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE_SQURE)
                    .map(|i| {
                        (0..NUM_PER_WORD_BATCH3)
                            .map(|j| ctx.internal(&format!("theta_sum_split_xor_{}_{}", i, j)))
                            .collect()
                    })
                    .collect();
                let setup_theta_sum_split_xor_vec = theta_sum_split_xor_vec.clone();

                let rho_bit_0: Vec<Queriable<F>> = (0..15)
                    .map(|i| ctx.internal(&format!("rho_bit0_{}", i)))
                    .collect();
                let setup_rho_bit_0 = rho_bit_0.clone();

                let rho_bit_1: Vec<Queriable<F>> = (0..15)
                    .map(|i| ctx.internal(&format!("rho_bit1_{}", i)))
                    .collect();
                let setup_rho_bit_1 = rho_bit_1.clone();

                let chi_split_value_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE_SQURE)
                    .map(|i| {
                        (0..NUM_PER_WORD_BATCH3)
                            .map(|j| ctx.internal(&format!("chi_split_value_{}_{}", i, j)))
                            .collect()
                    })
                    .collect();
                let setup_chi_split_value_vec: Vec<Vec<Queriable<F>>> = chi_split_value_vec.clone();

                let final_xor_split_vec: Vec<Queriable<F>> = (0..NUM_PER_WORD_BATCH4)
                    .map(|i| ctx.internal(&format!("final_xor_split_{}", i)))
                    .collect();
                let setup_final_xor_split_vec = final_xor_split_vec.clone();

                let final_sum_split_vec: Vec<Queriable<F>> = (0..NUM_PER_WORD_BATCH4)
                    .map(|i| ctx.internal(&format!("final_sum_split_{}", i)))
                    .collect();
                let setup_final_sum_split_vec = final_sum_split_vec.clone();
                let round_cst: Queriable<F> = ctx.internal("round constant");

                let mut hash_rlc = data_rlc;
                let mut next_round = round;
                if last == 0 {
                    next_round = ctx.internal("next_round");
                } else {
                    hash_rlc = ctx.internal("hash_rlc");
                }

                let mut squeeze_split_vec: Vec<Vec<Queriable<F>>> = Vec::new();
                if last == 1 {
                    squeeze_split_vec = (0..SQUEEZE_VECTOR_NUM)
                        .map(|i| {
                            (0..SQUEEZE_SPLIT_NUM / 2)
                                .map(|j| ctx.internal(&format!("squeeze_split_vec_{}_{}", i, j)))
                                .collect()
                        })
                        .collect();
                }
                let setup_squeeze_split_vec = squeeze_split_vec.clone();

                let mut squeeze_split_output_vec: Vec<Vec<Queriable<F>>> = Vec::new();
                if last == 1 {
                    squeeze_split_output_vec = (0..SQUEEZE_VECTOR_NUM)
                        .map(|i| {
                            (0..SQUEEZE_SPLIT_NUM / 2)
                                .map(|j| {
                                    ctx.internal(&format!("squeeze_split_output_vec_{}_{}", i, j))
                                })
                                .collect()
                        })
                        .collect();
                }
                let setup_squeeze_split_output_vec = squeeze_split_output_vec.clone();

                let mut s_new_vec: Vec<Queriable<F>> = Vec::new();
                if last == 1 {
                    s_new_vec = (0..PART_SIZE_SQURE)
                        .map(|i| {
                            ctx.internal(&format!("s_new[{}][{}]", i / PART_SIZE, i % PART_SIZE))
                        })
                        .collect();
                }
                let setup_s_new_vec = s_new_vec.clone();

                ctx.setup(move |ctx| {
                    let mut t_vec = vec![0; PART_SIZE_SQURE as usize];
                    {
                        let mut i: usize = 1;
                        let mut j: usize = 0;
                        for t in 0..PART_SIZE_SQURE {
                            if t == 0 {
                                i = 0;
                                j = 0
                            } else if t == 1 {
                                i = 1;
                                j = 0;
                            } else {
                                let m = j;
                                j = (2 * i + 3 * j) % PART_SIZE as usize;
                                i = m;
                            }
                            t_vec[i * PART_SIZE as usize + j] = t;
                        }
                    }

                    // Theta
                    let mut tmp_theta_sum_split_xor_vec = Vec::new();
                    let mut tmp_theta_sum_move_split_xor_vec = Vec::new();
                    for s in 0..PART_SIZE as usize {
                        // 1. \sum_y' a[x][y'][z]
                        // 2. xor(sum)
                        let mut sum_split_vec = setup_theta_split_vec[s][NUM_PER_WORD as usize] * 8
                            + setup_theta_split_vec[s][NUM_PER_WORD as usize - 1];
                        let mut sum_split_xor_vec =
                            setup_theta_split_xor_vec[s][NUM_PER_WORD as usize] * 8
                                + setup_theta_split_xor_vec[s][NUM_PER_WORD as usize - 1];
                        let mut sum_split_xor_move_value_vec =
                            setup_theta_split_xor_vec[s][NUM_PER_WORD as usize - 1] * 1;
                        for k in 1..NUM_PER_WORD as usize {
                            sum_split_vec = sum_split_vec * 64
                                + setup_theta_split_vec[s][NUM_PER_WORD as usize - k - 1];
                            sum_split_xor_vec = sum_split_xor_vec * 64
                                + setup_theta_split_xor_vec[s][NUM_PER_WORD as usize - k - 1];
                            sum_split_xor_move_value_vec = sum_split_xor_move_value_vec * 64
                                + setup_theta_split_xor_vec[s][NUM_PER_WORD as usize - k - 1];
                        }
                        sum_split_xor_move_value_vec = sum_split_xor_move_value_vec * 8
                            + setup_theta_split_xor_vec[s][NUM_PER_WORD as usize];

                        for k in 0..NUM_PER_WORD as usize {
                            ctx.add_lookup(
                                param
                                    .xor_table
                                    .apply(setup_theta_split_vec[s][k])
                                    .apply(setup_theta_split_xor_vec[s][k]),
                            );
                        }

                        ctx.constr(eq(
                            setup_s_vec[s * PART_SIZE as usize]
                                + setup_s_vec[s * PART_SIZE as usize + 1]
                                + setup_s_vec[s * PART_SIZE as usize + 2]
                                + setup_s_vec[s * PART_SIZE as usize + 3]
                                + setup_s_vec[s * PART_SIZE as usize + 4],
                            sum_split_vec,
                        ));

                        tmp_theta_sum_split_xor_vec.push(sum_split_xor_vec);
                        tmp_theta_sum_move_split_xor_vec.push(sum_split_xor_move_value_vec);
                    }

                    let mut rho_index = 0;
                    for i in 0..PART_SIZE as usize {
                        for j in 0..PART_SIZE as usize {
                            // Theta
                            // 3. a[x][y][z] = a[x][y][z] + xor(\sum_y' a[x-1][y'][z]) + xor(\sum
                            // a[x+1][y'][z-1]) 4. a'[x][y][z'+(t+1)(t+2)/2] =
                            // xor(a[x][y][z'+(t+1)(t+2)/2]) rho
                            // a[x][y][z'] = a[x][y][z']
                            let v = ((t_vec[i * PART_SIZE as usize + j] + 1)
                                * t_vec[i * PART_SIZE as usize + j]
                                / 2)
                                % NUM_BITS_PER_WORD;

                            for k in 0..NUM_PER_WORD_BATCH3 as usize {
                                ctx.add_lookup(
                                    param
                                        .xor_table_batch3
                                        .apply(
                                            setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [k],
                                        )
                                        .apply(
                                            setup_theta_sum_split_xor_vec
                                                [i * PART_SIZE as usize + j][k],
                                        ),
                                );
                            }

                            let mut tmp_theta_sum_split;
                            if v % 3 == 0 {
                                let st = (v / 3) as usize;
                                if st != 0 {
                                    tmp_theta_sum_split = setup_theta_sum_split_vec
                                        [i * PART_SIZE as usize + j][st - 1]
                                        * 1;
                                    for k in 1..st {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 512
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [st - k - 1];
                                    }
                                    tmp_theta_sum_split = tmp_theta_sum_split * 8
                                        + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                            [NUM_PER_WORD_BATCH3 as usize - 1];
                                    for k in 1..NUM_PER_WORD_BATCH3 as usize - st {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 512
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - k - 1];
                                    }
                                } else {
                                    tmp_theta_sum_split = setup_theta_sum_split_vec
                                        [i * PART_SIZE as usize + j]
                                        [NUM_PER_WORD_BATCH3 as usize - 1]
                                        * 1;
                                    for k in 1..NUM_PER_WORD_BATCH3 as usize {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 512
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - k - 1];
                                    }
                                }
                            } else if v % 3 == 1 {
                                let st = ((v - 1) / 3) as usize;
                                tmp_theta_sum_split = setup_rho_bit_1[rho_index] * 1;
                                for k in 0..st {
                                    tmp_theta_sum_split = tmp_theta_sum_split * 512
                                        + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                            [st - k - 1];
                                }
                                for k in 0..NUM_PER_WORD_BATCH3 as usize - st - 1 {
                                    if k == 0 {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 8
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - 1];
                                    } else {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 512
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - k - 1];
                                    }
                                }
                                tmp_theta_sum_split =
                                    tmp_theta_sum_split * 64 + setup_rho_bit_0[rho_index];
                                ctx.constr(eq(
                                    setup_rho_bit_0[rho_index] * 8 + setup_rho_bit_1[rho_index],
                                    setup_theta_sum_split_vec[i * PART_SIZE as usize + j][st],
                                ));
                                rho_index += 1;
                            } else {
                                let st = ((v - 2) / 3) as usize;
                                tmp_theta_sum_split = setup_rho_bit_1[rho_index] * 1;
                                for k in 0..st {
                                    tmp_theta_sum_split = tmp_theta_sum_split * 512
                                        + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                            [st - k - 1];
                                }
                                for k in 0..NUM_PER_WORD_BATCH3 as usize - st - 1 {
                                    if k == 0 {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 8
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - 1];
                                    } else {
                                        tmp_theta_sum_split = tmp_theta_sum_split * 512
                                            + setup_theta_sum_split_vec[i * PART_SIZE as usize + j]
                                                [NUM_PER_WORD_BATCH3 as usize - k - 1];
                                    }
                                }
                                tmp_theta_sum_split =
                                    tmp_theta_sum_split * 8 + setup_rho_bit_0[rho_index];
                                ctx.constr(eq(
                                    setup_rho_bit_0[rho_index] * 64 + setup_rho_bit_1[rho_index],
                                    setup_theta_sum_split_vec[i * PART_SIZE as usize + j][st],
                                ));
                                rho_index += 1;
                            }

                            ctx.constr(eq(
                                tmp_theta_sum_split,
                                setup_s_vec[i * PART_SIZE as usize + j]
                                    + tmp_theta_sum_split_xor_vec
                                        [(i + PART_SIZE as usize - 1) % PART_SIZE as usize]
                                        .clone()
                                    + tmp_theta_sum_move_split_xor_vec
                                        [(i + 1) % PART_SIZE as usize]
                                        .clone(),
                            ));
                        }
                    }

                    let mut tmp_pi_sum_split_xor_vec = setup_theta_sum_split_xor_vec.clone();
                    for i in 0..PART_SIZE as usize {
                        for j in 0..PART_SIZE as usize {
                            tmp_pi_sum_split_xor_vec
                                [j * PART_SIZE as usize + ((2 * i + 3 * j) % PART_SIZE as usize)] =
                                setup_theta_sum_split_xor_vec[i * PART_SIZE as usize + j].clone();
                        }
                    }

                    // chi
                    // a[x] = a[x] ^ (~a[x+1] & a[x+2])
                    // chi(3 - 2a[x] + a[x+1] - a[x+2])
                    ctx.add_lookup(param.constants_table.apply(round).apply(round_cst));
                    for i in 0..PART_SIZE as usize {
                        for j in 0..PART_SIZE as usize {
                            for k in 0..NUM_PER_WORD_BATCH3 as usize {
                                ctx.add_lookup(
                                    param
                                        .chi_table
                                        .apply(
                                            tmp_pi_sum_split_xor_vec[((i + 1)
                                                % PART_SIZE as usize)
                                                * PART_SIZE as usize
                                                + j][k]
                                                - tmp_pi_sum_split_xor_vec
                                                    [i * PART_SIZE as usize + j][k]
                                                - tmp_pi_sum_split_xor_vec
                                                    [i * PART_SIZE as usize + j][k]
                                                - tmp_pi_sum_split_xor_vec[((i + 2)
                                                    % PART_SIZE as usize)
                                                    * PART_SIZE as usize
                                                    + j][k]
                                                + 219,
                                        )
                                        .apply(
                                            setup_chi_split_value_vec[i * PART_SIZE as usize + j]
                                                [k],
                                        ),
                                );
                            }

                            let mut tmp_sum_split_chi_vec = setup_chi_split_value_vec
                                [i * PART_SIZE as usize + j]
                                [NUM_PER_WORD_BATCH3 as usize - 1]
                                * 1;
                            for k in 1..NUM_PER_WORD_BATCH3 as usize {
                                tmp_sum_split_chi_vec = tmp_sum_split_chi_vec * 512
                                    + setup_chi_split_value_vec[i * PART_SIZE as usize + j]
                                        [NUM_PER_WORD_BATCH3 as usize - k - 1];
                            }

                            if i != 0 || j != 0 {
                                if last == 1 {
                                    ctx.transition(eq(
                                        tmp_sum_split_chi_vec,
                                        setup_s_new_vec[i * PART_SIZE as usize + j],
                                    ));
                                } else {
                                    ctx.transition(eq(
                                        tmp_sum_split_chi_vec,
                                        setup_s_vec[i * PART_SIZE as usize + j].next(),
                                    ));
                                }
                            } else {
                                let mut tmp_sum_s_split_vec =
                                    setup_final_sum_split_vec[NUM_PER_WORD_BATCH4 as usize - 1] * 1;
                                let mut tmp_sum_s_split_xor_vec =
                                    setup_final_xor_split_vec[NUM_PER_WORD_BATCH4 as usize - 1] * 1;
                                ctx.add_lookup(
                                    param
                                        .xor_table_batch4
                                        .apply(
                                            setup_final_sum_split_vec
                                                [NUM_PER_WORD_BATCH4 as usize - 1],
                                        )
                                        .apply(
                                            setup_final_xor_split_vec
                                                [NUM_PER_WORD_BATCH4 as usize - 1],
                                        ),
                                );
                                for (&value, &xor_value) in setup_final_sum_split_vec
                                    .iter()
                                    .zip(setup_final_xor_split_vec.iter())
                                    .rev()
                                    .skip(1)
                                {
                                    tmp_sum_s_split_vec = tmp_sum_s_split_vec * 64 * 64 + value;
                                    tmp_sum_s_split_xor_vec =
                                        tmp_sum_s_split_xor_vec * 64 * 64 + xor_value;
                                    ctx.add_lookup(
                                        param.xor_table_batch4.apply(value).apply(xor_value),
                                    );
                                }

                                ctx.constr(eq(
                                    tmp_sum_s_split_vec,
                                    tmp_sum_split_chi_vec + round_cst,
                                ));
                                if last == 1 {
                                    ctx.transition(eq(
                                        tmp_sum_s_split_xor_vec,
                                        setup_s_new_vec[i * PART_SIZE as usize + j],
                                    ));
                                } else {
                                    ctx.transition(eq(
                                        tmp_sum_s_split_xor_vec,
                                        setup_s_vec[i * PART_SIZE as usize + j].next(),
                                    ));
                                }
                            }
                        }
                    }

                    if last == 1 {
                        for i in 0..SQUEEZE_VECTOR_NUM as usize {
                            let mut tmp_squeeze_split_sum =
                                setup_squeeze_split_vec[i][SQUEEZE_SPLIT_NUM as usize / 2 - 1] * 1;
                            for j in 1..SQUEEZE_SPLIT_NUM as usize / 2 {
                                tmp_squeeze_split_sum = tmp_squeeze_split_sum * 4096 * 4096
                                    + setup_squeeze_split_vec[i]
                                        [SQUEEZE_SPLIT_NUM as usize / 2 - j - 1];
                            }
                            ctx.constr(eq(
                                tmp_squeeze_split_sum,
                                setup_s_new_vec[i * PART_SIZE as usize],
                            ));
                            for j in 0..SQUEEZE_SPLIT_NUM as usize / 2 {
                                ctx.add_lookup(
                                    param
                                        .pack_table
                                        .apply(setup_squeeze_split_vec[i][j])
                                        .apply(setup_squeeze_split_output_vec[i][j]),
                                );
                            }
                            // hash_rlc
                            let mut tmp_hash_rlc_value = setup_squeeze_split_output_vec[0][0] * 1;

                            for (i, values) in setup_squeeze_split_output_vec.iter().enumerate() {
                                for (j, &value) in values
                                    .iter()
                                    .enumerate()
                                    .take(SQUEEZE_SPLIT_NUM as usize / 2)
                                {
                                    if i != 0 || j != 0 {
                                        tmp_hash_rlc_value = tmp_hash_rlc_value * 256 + value;
                                    }
                                }
                            }
                        }
                    }

                    if last == 1 {
                        ctx.constr(eq(round + 1, NUM_ROUNDS));
                        ctx.constr(eq(input_len, input_acc));
                        ctx.constr(eq(padded, 1));
                    } else {
                        ctx.constr(eq((round + 1 - next_round) * next_round, 0));
                        // xor((round + 1 = next_round), (round + 1 = NUM_ROUNDS))
                        // (round + 1 - next_round) / NUM_ROUNDS = 0, round < 23;  1, round = 23
                        // (round + 1 - NUM_ROUNDS) / (NUM_ROUNDS - next_round) = 1,round < 23; 0,
                        // round = 23 (round + 1 - next_round) / NUM_ROUNDS
                        // + (round + 1 - NUM_ROUNDS) / (NUM_ROUNDS - next_round)
                        // - 2 * ((round + 1 - next_round) / NUM_ROUNDS) * ((round + 1 - NUM_ROUNDS)
                        //   / (NUM_ROUNDS - next_round)) = 1
                        // (round + 1 - next_round) * (NUM_ROUNDS - next_round) + (round + 1 -
                        // NUM_ROUNDS) * NUM_ROUNDS + 2 * (round + 1 -
                        // next_round) * (round + 1 - NUM_ROUNDS) = NUM_ROUNDS * (NUM_ROUNDS -
                        // next_round)
                        ctx.constr(eq(
                            (round + 1 - next_round) * (next_round - NUM_ROUNDS)
                                + (round + 1 - NUM_ROUNDS) * NUM_ROUNDS
                                - (round + 1 - next_round) * (round + 1 - NUM_ROUNDS) * 2,
                            (next_round - NUM_ROUNDS) * NUM_ROUNDS,
                        ));
                        ctx.transition(eq(next_round, round.next()));
                        ctx.transition(eq(input_len, input_len.next()));
                        ctx.transition(eq(data_rlc, data_rlc.next()));
                        ctx.transition(eq(padded, padded.next()));
                    }
                });

                ctx.wg::<OneRoundValues<F>, _>(move |ctx, values| {
                    ctx.assign(round, values.round);
                    ctx.assign(round_cst, values.round_cst);
                    if last == 0 {
                        ctx.assign(next_round, values.next_round);
                    }
                    for (q, v) in s_vec.iter().zip(values.s_vec.iter()) {
                        ctx.assign(*q, *v)
                    }
                    for (q_vec, v_vec) in theta_split_vec.iter().zip(values.theta_split_vec.iter())
                    {
                        for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                    }
                    for (q_vec, v_vec) in theta_split_xor_vec
                        .iter()
                        .zip(values.theta_split_xor_vec.iter())
                    {
                        for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                    }
                    for (q_vec, v_vec) in theta_sum_split_vec
                        .iter()
                        .zip(values.theta_sum_split_vec.iter())
                    {
                        for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                    }
                    for (q_vec, v_vec) in theta_sum_split_xor_vec
                        .iter()
                        .zip(values.theta_sum_split_xor_vec.iter())
                    {
                        for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                    }
                    for (q, v) in rho_bit_0.iter().zip(values.rho_bit_0.iter()) {
                        ctx.assign(*q, *v)
                    }
                    for (q, v) in rho_bit_1.iter().zip(values.rho_bit_1.iter()) {
                        ctx.assign(*q, *v)
                    }
                    for (q_vec, v_vec) in chi_split_value_vec
                        .iter()
                        .zip(values.chi_split_value_vec.iter())
                    {
                        for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                    }
                    for (q, v) in final_sum_split_vec
                        .iter()
                        .zip(values.final_sum_split_vec.iter())
                    {
                        ctx.assign(*q, *v)
                    }
                    for (q, v) in final_xor_split_vec
                        .iter()
                        .zip(values.final_xor_split_vec.iter())
                    {
                        ctx.assign(*q, *v)
                    }
                    if last == 1 {
                        for (q, v) in s_new_vec.iter().zip(values.svalues.s_new_vec.iter()) {
                            ctx.assign(*q, *v)
                        }
                        for (q_vec, v_vec) in squeeze_split_vec
                            .iter()
                            .zip(values.svalues.squeeze_split_vec.iter())
                        {
                            for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(*q, *v)
                            }
                        }
                        for (q_vec, v_vec) in squeeze_split_output_vec
                            .iter()
                            .zip(values.svalues.squeeze_split_output_vec.iter())
                        {
                            for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(*q, *v)
                            }
                        }
                        ctx.assign(hash_rlc, values.svalues.hash_rlc);
                    }
                    ctx.assign(input_len, values.input_len);
                    ctx.assign(data_rlc, values.data_rlc);
                    ctx.assign(input_acc, values.input_acc);
                    ctx.assign(padded, values.padded);
                })
            })
        })
        .collect();

    ctx.pragma_first_step(&keccak_first_step); // keccak_pre_step
    ctx.pragma_last_step(&keccak_one_round_step_vec[1]); // keccak_squeeze_step
    ctx.pragma_num_steps(param.step_num);

    ctx.trace(move |ctx, params| {
        let input_num = params.bytes.len();
        let mut bits = convert_bytes_to_bits(params.bytes);
        println!("intput bits(without padding) = {:?}", bits);
        // padding
        bits.push(1);
        while (bits.len() + 1) % RATE_IN_BITS as usize != 0 {
            bits.push(0);
        }
        bits.push(1);
        println!("intput bits(with padding) = {:?}", bits);

        let mut s_new = [F::ZERO; PART_SIZE_SQURE as usize];

        // chunks
        let chunks = bits.chunks(RATE_IN_BITS as usize);
        let chunks_len = chunks.len();
        let mut data_rlc_value = F::ZERO;
        let mut input_acc = F::ZERO;
        // absorb
        for (k, chunk) in chunks.enumerate() {
            let s: Vec<F> = s_new.to_vec();
            let absorbs: Vec<F> = (0..PART_SIZE_SQURE as usize)
                .map(|idx| {
                    let i = idx % PART_SIZE as usize;
                    let j = idx / PART_SIZE as usize;
                    let mut absorb = F::ZERO;
                    if idx < NUM_WORDS_TO_ABSORB as usize {
                        absorb = pack(&chunk[idx * 64..(idx + 1) * 64]);
                        s_new[i * PART_SIZE as usize + j] =
                            field_xor(s[i * PART_SIZE as usize + j], absorb);
                    } else {
                        s_new[i * PART_SIZE as usize + j] = s[i * PART_SIZE as usize + j];
                    }
                    absorb
                })
                .collect();

            let absorb_split_vec: Vec<Vec<F>> = (0..NUM_WORDS_TO_ABSORB as usize)
                .map(|idx| {
                    let bits = chunk[idx * 64..(idx + 1) * 64].to_vec();
                    (0..SQUEEZE_SPLIT_NUM as usize / 2)
                        .map(|k| {
                            F::from(
                                bits[k * 8] as u64
                                    + bits[k * 8 + 1] as u64 * 8
                                    + bits[k * 8 + 2] as u64 * 64
                                    + bits[k * 8 + 3] as u64 * 512
                                    + bits[k * 8 + 4] as u64 * 4096
                                    + bits[k * 8 + 5] as u64 * 8 * 4096
                                    + bits[k * 8 + 6] as u64 * 64 * 4096
                                    + bits[k * 8 + 7] as u64 * 512 * 4096,
                            )
                        })
                        .collect()
                })
                .collect();

            let absorb_split_input_vec: Vec<Vec<F>> = (0..NUM_WORDS_TO_ABSORB as usize)
                .map(|idx| {
                    let bits = chunk[idx * 64..(idx + 1) * 64].to_vec();
                    (0..SQUEEZE_SPLIT_NUM as usize / 2)
                        .map(|k| {
                            F::from(
                                bits[k * 8] as u64
                                    + bits[k * 8 + 1] as u64 * 2
                                    + bits[k * 8 + 2] as u64 * 4
                                    + bits[k * 8 + 3] as u64 * 8
                                    + bits[k * 8 + 4] as u64 * 16
                                    + bits[k * 8 + 5] as u64 * 32
                                    + bits[k * 8 + 6] as u64 * 64
                                    + bits[k * 8 + 7] as u64 * 128,
                            )
                        })
                        .collect()
                })
                .collect();

            let mut is_padding_vec = vec![vec![F::ONE; 8]; NUM_WORDS_TO_ABSORB as usize];
            is_padding_vec = is_padding_vec
                .iter()
                .enumerate()
                .map(|(i, is_paddings)| {
                    is_paddings
                        .iter()
                        .enumerate()
                        .take(8)
                        .map(|(j, &is_padding)| {
                            if input_num > k * 8 * NUM_WORDS_TO_ABSORB as usize + i * 8 + j {
                                F::ZERO
                            } else {
                                is_padding
                            }
                        })
                        .collect()
                })
                .collect();

            let mut padded = F::ZERO;
            if k == 0 {
                let data_rlc = data_rlc_value;
                let data_rlc_vec: Vec<Vec<F>> = absorb_split_input_vec
                    .iter()
                    .zip(is_padding_vec.iter())
                    .map(|(v1_vec, v2_vec)| {
                        v1_vec
                            .iter()
                            .zip(v2_vec.iter())
                            .map(|(&v1, &v2)| {
                                if v2 == F::ZERO {
                                    data_rlc_value = data_rlc_value * F::from(256) + v1
                                }
                                data_rlc_value
                            })
                            .collect()
                    })
                    .collect();

                let values = PreValues {
                    s_vec: s,
                    absorb_rows: absorbs[0..NUM_WORDS_TO_ABSORB as usize].to_vec(),
                    round_value: F::ZERO,
                    absorb_split_vec,
                    absorb_split_input_vec,
                    split_values: Vec::new(),
                    is_padding_vec: is_padding_vec.clone(),
                    input_len: F::from(input_num as u64),
                    data_rlc_vec,
                    data_rlc,
                    input_acc,
                    padded,
                };
                ctx.add(&keccak_first_step, values);
            } else {
                let data_rlc = data_rlc_value;
                let split_values = (0..NUM_WORDS_TO_ABSORB as usize)
                    .map(|t| {
                        let i = t % PART_SIZE as usize;
                        let j = t / PART_SIZE as usize;
                        let v = i * PART_SIZE as usize + j;
                        eval_keccak_f_to_bit_vec4::<F>(
                            s[v] + absorbs[(v % PART_SIZE as usize) * PART_SIZE as usize
                                + (v / PART_SIZE as usize)],
                            s_new[v],
                        )
                    })
                    .collect();

                let data_rlc_vec: Vec<Vec<F>> = absorb_split_input_vec
                    .iter()
                    .zip(is_padding_vec.iter())
                    .map(|(v1_vec, v2_vec)| {
                        v1_vec
                            .iter()
                            .zip(v2_vec.iter())
                            .map(|(&v1, &v2)| {
                                if v2 == F::ZERO {
                                    data_rlc_value = data_rlc_value * F::from(256) + v1
                                }
                                data_rlc_value
                            })
                            .collect()
                    })
                    .collect();
                let values = PreValues {
                    s_vec: s,
                    absorb_rows: absorbs[0..NUM_WORDS_TO_ABSORB as usize].to_vec(),
                    split_values,
                    absorb_split_vec,
                    absorb_split_input_vec,
                    round_value: F::ZERO,
                    is_padding_vec: is_padding_vec.clone(),
                    input_len: F::from(input_num as u64),
                    data_rlc_vec,
                    data_rlc,
                    input_acc,
                    padded,
                };
                ctx.add(&keccak_pre_step, values);
            }
            padded = is_padding_vec[NUM_WORDS_TO_ABSORB as usize - 1][7];

            input_acc = is_padding_vec.iter().fold(input_acc, |acc, is_paddings| {
                let v = is_paddings
                    .iter()
                    .fold(F::ZERO, |acc, is_padding| acc + (F::ONE - is_padding));
                acc + v
            });

            for (round, &cst) in ROUND_CST.iter().enumerate().take(NUM_ROUNDS as usize) {
                let mut values = eval_keccak_f_one_round(
                    round as u64,
                    cst,
                    s_new.to_vec(),
                    input_num as u64,
                    data_rlc_value,
                    input_acc,
                    padded,
                );
                s_new = values.s_new_vec.clone().try_into().unwrap();

                if k != chunks_len - 1 || round != NUM_ROUNDS as usize - 1 {
                    ctx.add(&keccak_one_round_step_vec[0], values.clone());
                } else {
                    // squeezing
                    let mut squeeze_split_vec: Vec<Vec<F>> = Vec::new();
                    let mut squeeze_split_output_vec: Vec<Vec<F>> = Vec::new();
                    for i in 0..4 {
                        let bits = convert_field_to_vec_bits(s_new[(i * PART_SIZE) as usize]);

                        squeeze_split_vec.push(
                            (0..SQUEEZE_SPLIT_NUM as usize / 2)
                                .map(|k| {
                                    let value = bits[k * 8] as u64
                                        + bits[k * 8 + 1] as u64 * 8
                                        + bits[k * 8 + 2] as u64 * 64
                                        + bits[k * 8 + 3] as u64 * 512
                                        + bits[k * 8 + 4] as u64 * 4096
                                        + bits[k * 8 + 5] as u64 * 8 * 4096
                                        + bits[k * 8 + 6] as u64 * 64 * 4096
                                        + bits[k * 8 + 7] as u64 * 512 * 4096;
                                    F::from(value)
                                })
                                .collect(),
                        );
                        squeeze_split_output_vec.push(
                            (0..SQUEEZE_SPLIT_NUM as usize / 2)
                                .map(|k| {
                                    let value = bits[k * 8] as u64
                                        + bits[k * 8 + 1] as u64 * 2
                                        + bits[k * 8 + 2] as u64 * 4
                                        + bits[k * 8 + 3] as u64 * 8
                                        + bits[k * 8 + 4] as u64 * 16
                                        + bits[k * 8 + 5] as u64 * 32
                                        + bits[k * 8 + 6] as u64 * 64
                                        + bits[k * 8 + 7] as u64 * 128;
                                    F::from(value)
                                })
                                .collect(),
                        );
                    }
                    let mut hash_rlc = F::ZERO;
                    for squeeze_split_output in squeeze_split_output_vec.iter().take(4) {
                        for output in squeeze_split_output
                            .iter()
                            .take(SQUEEZE_SPLIT_NUM as usize / 2)
                        {
                            hash_rlc = hash_rlc * F::from(256) + output;
                        }
                    }
                    values.svalues = SqueezeValues {
                        s_new_vec: s_new.to_vec(),
                        squeeze_split_vec,
                        squeeze_split_output_vec,
                        hash_rlc,
                    };
                    ctx.add(&keccak_one_round_step_vec[1], values);
                }
            }
        }

        let output2: Vec<Vec<u8>> = (0..4)
            .map(|k| {
                pack_with_base::<F>(
                    &convert_field_to_vec_bits(s_new[(k * PART_SIZE) as usize]),
                    2,
                )
                .to_repr()
                .into_iter()
                .take(8)
                .collect::<Vec<_>>()
                .to_vec()
            })
            .collect();
        println!("output = {:x?}", output2.concat());
    });
}

#[derive(Default)]
struct KeccakCircuit {
    // pub bits: Vec<u8>,
    pub bytes: Vec<u8>,
}

struct CircuitParams {
    pub constants_table: LookupTable,
    pub xor_table: LookupTable,
    pub xor_table_batch3: LookupTable,
    pub xor_table_batch4: LookupTable,
    pub chi_table: LookupTable,
    pub pack_table: LookupTable,
    pub step_num: usize,
}

fn keccak_super_circuit<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    input_len: usize,
) -> SuperCircuit<F, KeccakCircuit> {
    super_circuit::<F, KeccakCircuit, _>("keccak", |ctx| {
        let in_n = (input_len * 8 + 1 + RATE_IN_BITS as usize) / RATE_IN_BITS as usize;
        let step_num = in_n * (1 + NUM_ROUNDS as usize);

        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        // config(SingleRowCellManager {}, LogNSelectorBuilder {});

        let (_, constants_table) = ctx.sub_circuit(
            single_config.clone(),
            keccak_round_constants_table,
            NUM_ROUNDS as usize + 1,
        );
        let (_, xor_table) = ctx.sub_circuit(single_config.clone(), keccak_xor_table_batch2, 36);
        let (_, xor_table_batch3) =
            ctx.sub_circuit(single_config.clone(), keccak_xor_table_batch3, 64);
        let (_, xor_table_batch4) =
            ctx.sub_circuit(single_config.clone(), keccak_xor_table_batch4, 81);
        let (_, chi_table) = ctx.sub_circuit(single_config.clone(), keccak_chi_table, 125);
        let (_, pack_table) = ctx.sub_circuit(single_config, keccak_pack_table, 0);

        let params = CircuitParams {
            constants_table,
            xor_table,
            xor_table_batch3,
            xor_table_batch4,
            chi_table,
            pack_table,
            step_num,
        };

        let maxwidth_config = config(
            MaxWidthCellManager::new(198, true),
            SimpleStepSelectorBuilder {},
        );
        let (keccak, _) = ctx.sub_circuit(maxwidth_config, keccak_circuit, params);

        ctx.mapping(move |ctx, values| {
            ctx.map(&keccak, values);
        })
    })
}

use chiquito::plonkish::backend::plaf::chiquito2Plaf;
use polyexen::plaf::{Plaf, PlafDisplayBaseTOML, PlafDisplayFixedCSV, Witness, WitnessDisplayCSV};

fn write_files(name: &str, plaf: &Plaf, wit: &Witness) -> Result<(), io::Error> {
    let mut base_file = File::create(format!("{}.toml", name))?;
    let mut fixed_file = File::create(format!("{}_fixed.csv", name))?;
    let mut witness_file = File::create(format!("{}_witness.csv", name))?;

    write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
    write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
    write!(witness_file, "{}", WitnessDisplayCSV(wit))?;
    println!("write file success...{}", name);
    Ok(())
}

fn keccak_plaf(circuit_param: KeccakCircuit, k: u32) {
    let super_circuit = keccak_super_circuit::<Fr>(circuit_param.bytes.len());
    let witness = super_circuit.get_mapping().generate(circuit_param);

    for wit_gen in witness.values() {
        let wit_gen = wit_gen.clone();

        let mut circuit = super_circuit.get_sub_circuits()[0].clone();
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[1].columns);
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[2].columns);
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[3].columns);
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[4].columns);
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[5].columns);
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[6].columns);

        for (key, value) in super_circuit.get_sub_circuits()[0].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[1].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[2].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[3].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[4].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[5].fixed_assignments.iter() {
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }

        let (plaf, plaf_wit_gen) = chiquito2Plaf(circuit, k, false);

        let mut plaf = plaf;
        plaf.set_challenge_alias(0, "r_keccak".to_string());
        let wit = plaf_wit_gen.generate(Some(wit_gen));
        write_files("keccak_output", &plaf, &wit).unwrap();
    }
}

fn keccak_run(circuit_param: KeccakCircuit, k: u32) -> bool {
    let super_circuit = keccak_super_circuit::<Fr>(circuit_param.bytes.len());

    let compiled = chiquitoSuperCircuit2Halo2(&super_circuit);

    let circuit = ChiquitoHalo2SuperCircuit::new(
        compiled,
        super_circuit.get_mapping().generate(circuit_param),
    );

    let prover = MockProver::<Fr>::run(k, &circuit, Vec::new()).unwrap();
    let result = prover.verify();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
        false
    } else {
        true
    }
}

fn main() {
    let circuit_param = KeccakCircuit {
        bytes: vec![0, 1, 2, 3, 4, 5, 6, 7],
    };

    let res = keccak_run(circuit_param, 9);

    if res {
        keccak_plaf(
            KeccakCircuit {
                bytes: vec![0, 1, 2, 3, 4, 5, 6, 7],
            },
            11,
        );
    }
}
