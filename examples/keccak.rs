use chiquito::{
    ast::{query::Queriable, ASTExpr},
    frontend::dsl::{lb::LookupTable, super_circuit, CircuitContext},
    plonkish::{
        backend::halo2::{chiquitoSuperCircuit2Halo2, ChiquitoHalo2SuperCircuit},
        compiler::{
            cell_manager::{MaxWidthCellManager, SingleRowCellManager},
            config,
            step_selector::LogNSelectorBuilder,
        },
        ir::sc::SuperCircuit,
    },
};
use std::hash::Hash;

use halo2_proofs::{
    dev::MockProver,
    halo2curves::{bn256::Fr, group::ff::PrimeField},
};

use std::{
    fs::File,
    io::{self, Write},
};

const BIT_COUNT: usize = 3;
const PART_SIZE: usize = 5;
const NUM_BYTES_PER_WORD: usize = 8;
const NUM_BITS_PER_BYTE: usize = 8;
const NUM_WORDS_TO_ABSORB: usize = 17;
const RATE: usize = NUM_WORDS_TO_ABSORB * NUM_BYTES_PER_WORD;
const NUM_BITS_PER_WORD: usize = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE;
const NUM_PER_WORD: usize = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE / 2;
const RATE_IN_BITS: usize = RATE * NUM_BITS_PER_BYTE;
const NUM_ROUNDS: usize = 24;
const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

const NUM_PER_WORD_BATCH3: usize = 22;
const NUM_PER_WORD_BATCH4: usize = 16;

// const OUTPUT_LENGTH: usize = 256;
const SQUEEZE_VECTOR_NUM: usize = 4;
const SQUEEZE_SPLIT_NUM: usize = 16;

pub const ROUND_CST: [u64; NUM_ROUNDS + 1] = [
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
pub(crate) fn pack<F: PrimeField>(bits: &[u8]) -> F {
    pack_with_base(bits, BIT_SIZE)
}

/// Pack bits in the range [0,BIT_SIZE[ into a sparse keccak word with the
/// specified bit base
pub(crate) fn pack_with_base<F: PrimeField>(bits: &[u8], base: usize) -> F {
    // \sum 8^i * bit_i
    let base = F::from(base as u64);
    bits.iter()
        .rev()
        .fold(F::ZERO, |acc, &bit| acc * base + F::from(bit as u64))
}

/// Calculates a ^ b with a and b field elements
pub(crate) fn field_xor<F: PrimeField<Repr = [u8; 32]>>(a: F, b: F) -> F {
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

pub(crate) fn pack_u64<F: PrimeField>(value: u64) -> F {
    pack(
        &((0..NUM_BITS_PER_WORD)
            .map(|i| ((value >> i) & 1) as u8)
            .collect::<Vec<_>>()),
    )
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

fn convert_bits_to_f<F: PrimeField<Repr = [u8; 32]>>(value_vec: &Vec<u8>) -> F {
    assert_eq!(value_vec.len(), NUM_BITS_PER_WORD);
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

fn eval_keccak_f_to_bit_vec<F: PrimeField<Repr = [u8; 32]>>(
    value1: F,
    value2: F,
) -> (Vec<(F, F)>, F, F) {
    let v1_vec = convert_field_to_vec_bits(value1);
    let v2_vec = convert_field_to_vec_bits(value2);
    assert_eq!(v1_vec.len(), NUM_BITS_PER_WORD);
    assert_eq!(v2_vec.len(), NUM_BITS_PER_WORD);
    let vec = (0..NUM_PER_WORD)
        .map(|i| {
            (
                F::from_u128(v1_vec[2 * i] as u128 + v1_vec[2 * i + 1] as u128 * 8),
                F::from_u128(v2_vec[2 * i] as u128 + v2_vec[2 * i + 1] as u128 * 8),
            )
        })
        .collect();
    (
        vec,
        F::from_u128(v2_vec[NUM_BITS_PER_WORD - 2] as u128),
        F::from_u128(v2_vec[NUM_BITS_PER_WORD - 1] as u128),
    )
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
    ctx.pragma_num_steps(SQUEEZE_SPLIT_NUM * SQUEEZE_SPLIT_NUM);
    ctx.fixed_gen(move |ctx| {
        for i in 0..SQUEEZE_SPLIT_NUM {
            let index = (i / 8) * 512 + (i % 8) / 4 * 64 + (i % 4) / 2 * 8 + i % 2;
            for j in 0..SQUEEZE_SPLIT_NUM {
                let index_j = (j / 8) * 512 + (j % 8) / 4 * 64 + (j % 4) / 2 * 8 + j % 2;
                ctx.assign(
                    i * SQUEEZE_SPLIT_NUM + j,
                    lookup_pack_row,
                    F::from((index * 4096 + index_j) as u64),
                );
                ctx.assign(
                    i * SQUEEZE_SPLIT_NUM + j,
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
}

struct SqueezeValues<F> {
    s_vec: Vec<F>,
    squeeze_split_vec: Vec<Vec<F>>,
    squeeze_split_output_vec: Vec<Vec<F>>,
}

#[derive(Clone)]
struct OneRoundValues<F> {
    round: F,
    round_cst: F,

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
}

fn eval_keccak_f_one_round<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    round: u64,
    cst: u64,
    s_vec: Vec<F>,
) -> OneRoundValues<F> {
    let mut s_new_vec = Vec::new();
    let mut theta_split_vec = Vec::new();
    let mut theta_split_xor_vec = Vec::new();
    let mut theta_sum_split_xor_value_vec = Vec::new();
    let mut theta_sum_split_xor_move_value_vec = Vec::new();
    let mut theta_sum_split_vec = Vec::new();
    let mut theta_sum_split_xor_vec = Vec::new();
    let mut rho_pi_s_new_vec = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut rho_bit_0 = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut rho_bit_1 = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut chi_sum_value_vec = Vec::new();
    let mut chi_sum_split_value_vec = Vec::new();
    let mut chi_split_value_vec = Vec::new();
    let mut final_sum_split_vec = Vec::new();
    let mut final_xor_split_vec = Vec::new();

    let mut t_vec = vec![0; PART_SIZE * PART_SIZE];
    {
        let mut i = 1;
        let mut j = 0;
        for t in 0..PART_SIZE * PART_SIZE {
            if t == 0 {
                i = 0;
                j = 0
            } else if t == 1 {
                i = 1;
                j = 0;
            } else {
                let m = j;
                j = (2 * i + 3 * j) % PART_SIZE;
                i = m;
            }
            t_vec[i * PART_SIZE + j] = t;
        }
    }

    for i in 0..PART_SIZE {
        let sum = s_vec[i * PART_SIZE]
            + s_vec[i * PART_SIZE + 1]
            + s_vec[i * PART_SIZE + 2]
            + s_vec[i * PART_SIZE + 3]
            + s_vec[i * PART_SIZE + 4];
        let sum_bits = convert_field_to_vec_bits(sum);

        let xor: F = field_xor(
            field_xor(
                field_xor(
                    field_xor(s_vec[i * PART_SIZE], s_vec[i * PART_SIZE + 1]),
                    s_vec[i * PART_SIZE + 2],
                ),
                s_vec[i * PART_SIZE + 3],
            ),
            s_vec[i * PART_SIZE + 4],
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

    for i in 0..PART_SIZE {
        let xor = theta_sum_split_xor_value_vec[(i + PART_SIZE - 1) % PART_SIZE];
        let xor_rot = theta_sum_split_xor_move_value_vec[(i + 1) % PART_SIZE];
        for j in 0..PART_SIZE {
            let v =
                ((t_vec[i * PART_SIZE + j] + 1) * t_vec[i * PART_SIZE + j] / 2) % NUM_BITS_PER_WORD;
            let st = s_vec[i * PART_SIZE + j] + xor + xor_rot;
            let st_xor = field_xor(field_xor(s_vec[i * PART_SIZE + j], xor), xor_rot);
            let mut st_split = Vec::new();
            let mut st_split_xor = Vec::new();
            let mut st_bit_vec = convert_field_to_vec_bits(st);
            let mut st_bit_xor_vec = convert_field_to_vec_bits(st_xor);

            // rho
            // a[x][y][z] = a[x][y][z-(t+1)(t+2)/2]
            let mut b0 = F::ZERO;
            let mut b1 = F::ZERO;
            if v % 3 == 1 {
                b0 =
                    F::from(st_bit_vec[1] as u64) * F::from_u128(8) + F::from(st_bit_vec[0] as u64);
                b1 = F::from(st_bit_vec[NUM_BITS_PER_WORD - 1] as u64);
            } else if v % 3 == 2 {
                b0 = F::from(st_bit_vec[0] as u64);
                b1 = F::from(st_bit_vec[NUM_BITS_PER_WORD - 1] as u64) * F::from_u128(8)
                    + F::from(st_bit_vec[NUM_BITS_PER_WORD - 2] as u64)
            }
            rho_bit_0[i * PART_SIZE + j] = b0;
            rho_bit_1[i * PART_SIZE + j] = b1;

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
            st_split.push(F::from_u128(st_bit_vec[NUM_BITS_PER_WORD - 1] as u128));
            st_split_xor.push(F::from_u128(st_bit_xor_vec[NUM_BITS_PER_WORD - 1] as u128));

            theta_sum_split_vec.push(st_split);
            theta_sum_split_xor_vec.push(st_split_xor);

            // pi
            // a[y][2x + 3y] = a[x][y]
            rho_pi_s_new_vec[j * PART_SIZE + ((2 * i + 3 * j) % PART_SIZE)] =
                convert_bits_to_f(&st_bit_xor_vec);
        }
    }

    // chi
    // a[x] = a[x] ^ (~a[x+1] & a[x+2])
    for i in 0..PART_SIZE {
        for j in 0..PART_SIZE {
            let a_vec = convert_field_to_vec_bits(rho_pi_s_new_vec[i * PART_SIZE + j]);
            let b_vec = convert_field_to_vec_bits(rho_pi_s_new_vec[((i + 1) % 5) * PART_SIZE + j]);
            let c_vec = convert_field_to_vec_bits(rho_pi_s_new_vec[((i + 2) % 5) * PART_SIZE + j]);
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

            let sum_split_vec: Vec<F> = (0..NUM_PER_WORD_BATCH3)
                .map(|i| {
                    if i == NUM_PER_WORD_BATCH3 - 1 {
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
            let chi_split_vec: Vec<F> = (0..NUM_PER_WORD_BATCH3)
                .map(|i| {
                    if i == NUM_PER_WORD_BATCH3 - 1 {
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

    for i in 0..NUM_PER_WORD_BATCH4 {
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

    OneRoundValues {
        round: F::from(round),
        round_cst: pack_u64::<F>(cst),

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
    }
}

fn keccak_circuit<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    ctx: &mut CircuitContext<F, KeccakCircuit>,
    param: CircuitParams,
) {
    use chiquito::frontend::dsl::cb::*;

    let s_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
        .map(|i| ctx.forward(&format!("s[{}][{}]", i / PART_SIZE, i % PART_SIZE)))
        .collect();

    let round: Queriable<F> = ctx.forward("round");

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

        ctx.setup(move |ctx| {
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.constr(eq(setup_s_vec[i * PART_SIZE + j], 0));
                    if j * PART_SIZE + i < NUM_WORDS_TO_ABSORB {
                        // xor
                        // 000 xor 000/001 -> 000 + 000/001
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE + j] + setup_absorb_vec[j * PART_SIZE + i],
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));

                        let mut tmp_absorb_split_sum_vec = setup_absorb_split_vec
                            [j * PART_SIZE + i][SQUEEZE_SPLIT_NUM / 2 - 1]
                            * 1;
                        for k in 1..SQUEEZE_SPLIT_NUM / 2 {
                            tmp_absorb_split_sum_vec = tmp_absorb_split_sum_vec * 4096 * 4096
                                + setup_absorb_split_vec[j * PART_SIZE + i]
                                    [SQUEEZE_SPLIT_NUM / 2 - k - 1];
                        }
                        ctx.constr(eq(
                            setup_absorb_vec[j * PART_SIZE + i],
                            tmp_absorb_split_sum_vec,
                        ));
                        for k in 0..SQUEEZE_SPLIT_NUM / 2 {
                            ctx.add_lookup(
                                param
                                    .pack_table
                                    .apply(setup_absorb_split_vec[j * PART_SIZE + i][k])
                                    .apply(setup_absorb_split_input_vec[j * PART_SIZE + i][k]),
                            );
                        }
                    } else {
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE + j],
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));
                    }
                }
            }

            ctx.constr(eq(round, 0));
            ctx.transition(eq(round, round.next()));
        });

        ctx.wg::<PreValues<F>, _>(move |ctx, values| {
            // for i in 0..NUM_WORDS_TO_ABSORB {
            for (q, v) in absorb_vec
                .iter()
                .zip(values.absorb_rows.iter())
                .take(NUM_WORDS_TO_ABSORB)
            {
                ctx.assign(*q, *v)
            }

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.assign(s_vec[i * PART_SIZE + j], F::ZERO);
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
            ctx.assign(round, values.round_value);
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

        let sum_split_value_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| ctx.internal(&format!("sum_split_value_{}", i)))
            .collect();
        let setup_sum_split_value_vec = sum_split_value_vec.clone();

        let split_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..NUM_PER_WORD)
                    .map(|j| ctx.internal(&format!("split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_split_vec = split_vec.clone();

        let split_xor_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB)
            .map(|i| {
                (0..NUM_PER_WORD)
                    .map(|j| ctx.internal(&format!("split_xor_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_split_xor_vec = split_xor_vec.clone();

        ctx.setup(move |ctx| {
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    if j * PART_SIZE + i < NUM_WORDS_TO_ABSORB {
                        // xor
                        ctx.constr(eq(
                            setup_s_vec[i * PART_SIZE + j] + setup_absorb_vec[j * PART_SIZE + i],
                            setup_sum_split_value_vec[i * PART_SIZE + j],
                        ));

                        let mut tmp_absorb_split_sum_vec = setup_absorb_split_vec
                            [j * PART_SIZE + i][SQUEEZE_SPLIT_NUM / 2 - 1]
                            * 1;
                        for k in 1..SQUEEZE_SPLIT_NUM / 2 {
                            tmp_absorb_split_sum_vec = tmp_absorb_split_sum_vec * 4096 * 4096
                                + setup_absorb_split_vec[j * PART_SIZE + i]
                                    [SQUEEZE_SPLIT_NUM / 2 - k - 1];
                        }
                        ctx.constr(eq(
                            setup_absorb_vec[j * PART_SIZE + i],
                            tmp_absorb_split_sum_vec,
                        ));
                        for k in 0..SQUEEZE_SPLIT_NUM / 2 {
                            ctx.add_lookup(
                                param
                                    .pack_table
                                    .apply(setup_absorb_split_vec[j * PART_SIZE + i][k])
                                    .apply(setup_absorb_split_input_vec[j * PART_SIZE + i][k]),
                            );
                        }

                        for k in 0..NUM_PER_WORD {
                            ctx.add_lookup(
                                param
                                    .xor_table
                                    .apply(setup_split_vec[j * PART_SIZE + i][k])
                                    .apply(setup_split_xor_vec[j * PART_SIZE + i][k]),
                            );
                        }
                    } else {
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE + j],
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));
                    }
                }
            }

            for s in 0..NUM_WORDS_TO_ABSORB {
                // let s = (s % PART_SIZE) * PART_SIZE + s / PART_SIZE;

                let mut sum_split_vec: ASTExpr<F> = setup_split_vec[s][NUM_PER_WORD - 1] * 1;
                let mut sum_split_xor_vec: ASTExpr<F> =
                    setup_split_xor_vec[s][NUM_PER_WORD - 1] * 1;
                for (&value, &xor_value) in setup_split_vec[s]
                    .iter()
                    .rev()
                    .zip(setup_split_xor_vec[s].iter().rev())
                    .take(NUM_PER_WORD)
                    .skip(1)
                {
                    sum_split_vec = sum_split_vec * 64 + value;
                    sum_split_xor_vec = sum_split_xor_vec * 64 + xor_value;
                }
                ctx.constr(eq(
                    sum_split_vec,
                    setup_sum_split_value_vec[(s % PART_SIZE) * PART_SIZE + s / PART_SIZE],
                ));
                ctx.transition(eq(
                    sum_split_xor_vec,
                    setup_s_vec[(s % PART_SIZE) * PART_SIZE + s / PART_SIZE].next(),
                ));
            }

            ctx.transition(eq(round, round.next()));
        });

        ctx.wg::<PreValues<F>, _>(move |ctx, values| {
            ctx.assign(round, F::ZERO);
            for (q, v) in absorb_vec
                .iter()
                .zip(values.absorb_rows.iter())
                .take(NUM_WORDS_TO_ABSORB)
            {
                ctx.assign(*q, *v)
            }

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.assign(s_vec[i * PART_SIZE + j], F::ZERO);
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

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    if j * PART_SIZE + i < NUM_WORDS_TO_ABSORB {
                        ctx.assign(
                            sum_split_value_vec[i * PART_SIZE + j],
                            values.s_vec[i * PART_SIZE + j] + values.absorb_rows[j * PART_SIZE + i],
                        );
                        ctx.assign(
                            absorb_vec[j * PART_SIZE + i],
                            values.absorb_rows[j * PART_SIZE + i],
                        );
                    } else {
                        ctx.assign(
                            sum_split_value_vec[i * PART_SIZE + j],
                            values.s_vec[i * PART_SIZE + j],
                        );
                    }
                    ctx.assign(s_vec[i * PART_SIZE + j], values.s_vec[i * PART_SIZE + j]);
                }
            }

            for i in 0..NUM_WORDS_TO_ABSORB {
                for j in 0..NUM_PER_WORD {
                    ctx.assign(split_vec[i][j], values.split_values[i][j].0);
                    ctx.assign(split_xor_vec[i][j], values.split_values[i][j].1);
                }
            }
        })
    });

    let keccak_one_round = ctx.step_type_def("keccak one round", |ctx| {
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

        let theta_sum_split_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| {
                (0..NUM_PER_WORD_BATCH3)
                    .map(|j| ctx.internal(&format!("theta_sum_split_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_theta_sum_split_vec = theta_sum_split_vec.clone();

        let theta_sum_split_xor_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| {
                (0..NUM_PER_WORD_BATCH3)
                    .map(|j| ctx.internal(&format!("theta_sum_split_xor_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_theta_sum_split_xor_vec = theta_sum_split_xor_vec.clone();

        let rho_bit_0: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| ctx.internal(&format!("rho_bit0_{}", i)))
            .collect();
        let setup_rho_bit_0 = rho_bit_0.clone();

        let rho_bit_1: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| ctx.internal(&format!("rho_bit1_{}", i)))
            .collect();
        let setup_rho_bit_1 = rho_bit_1.clone();

        let chi_split_value_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE)
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

        ctx.setup(move |ctx| {
            let mut t_vec = vec![0; PART_SIZE * PART_SIZE];
            {
                let mut i = 1;
                let mut j = 0;
                for t in 0..PART_SIZE * PART_SIZE {
                    if t == 0 {
                        i = 0;
                        j = 0
                    } else if t == 1 {
                        i = 1;
                        j = 0;
                    } else {
                        let m = j;
                        j = (2 * i + 3 * j) % PART_SIZE;
                        i = m;
                    }
                    t_vec[i * PART_SIZE + j] = t;
                }
            }

            // Theta
            let mut tmp_theta_sum_split_xor_vec: Vec<ASTExpr<F>> = Vec::new();
            let mut tmp_theta_sum_move_split_xor_vec: Vec<ASTExpr<F>> = Vec::new();
            for s in 0..PART_SIZE {
                // 1. \sum_y' a[x][y'][z]
                // 2. xor(sum)
                let mut sum_split_vec: ASTExpr<F> = setup_theta_split_vec[s][NUM_PER_WORD] * 8
                    + setup_theta_split_vec[s][NUM_PER_WORD - 1];
                let mut sum_split_xor_vec: ASTExpr<F> = setup_theta_split_xor_vec[s][NUM_PER_WORD]
                    * 8
                    + setup_theta_split_xor_vec[s][NUM_PER_WORD - 1];
                let mut sum_split_xor_move_value_vec: ASTExpr<F> =
                    setup_theta_split_xor_vec[s][NUM_PER_WORD - 1] * 1;
                for k in 1..NUM_PER_WORD {
                    sum_split_vec =
                        sum_split_vec * 64 + setup_theta_split_vec[s][NUM_PER_WORD - k - 1];
                    sum_split_xor_vec =
                        sum_split_xor_vec * 64 + setup_theta_split_xor_vec[s][NUM_PER_WORD - k - 1];
                    sum_split_xor_move_value_vec = sum_split_xor_move_value_vec * 64
                        + setup_theta_split_xor_vec[s][NUM_PER_WORD - k - 1];
                }
                sum_split_xor_move_value_vec =
                    sum_split_xor_move_value_vec * 8 + setup_theta_split_xor_vec[s][NUM_PER_WORD];

                for k in 0..NUM_PER_WORD {
                    ctx.add_lookup(
                        param
                            .xor_table
                            .apply(setup_theta_split_vec[s][k])
                            .apply(setup_theta_split_xor_vec[s][k]),
                    );
                }

                ctx.constr(eq(
                    setup_s_vec[s * PART_SIZE]
                        + setup_s_vec[s * PART_SIZE + 1]
                        + setup_s_vec[s * PART_SIZE + 2]
                        + setup_s_vec[s * PART_SIZE + 3]
                        + setup_s_vec[s * PART_SIZE + 4],
                    sum_split_vec,
                ));

                tmp_theta_sum_split_xor_vec.push(sum_split_xor_vec);
                tmp_theta_sum_move_split_xor_vec.push(sum_split_xor_move_value_vec);
            }

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    // Theta
                    // 3. a[x][y][z] = a[x][y][z] + xor(\sum_y' a[x-1][y'][z]) + xor(\sum
                    // a[x+1][y'][z-1]) 4. a'[x][y][z'+(t+1)(t+2)/2] =
                    // xor(a[x][y][z'+(t+1)(t+2)/2]) rho
                    // a[x][y][z'] = a[x][y][z']
                    let v = ((t_vec[i * PART_SIZE + j] + 1) * t_vec[i * PART_SIZE + j] / 2)
                        % NUM_BITS_PER_WORD;

                    for k in 0..NUM_PER_WORD_BATCH3 {
                        ctx.add_lookup(
                            param
                                .xor_table_batch3
                                .apply(setup_theta_sum_split_vec[i * PART_SIZE + j][k])
                                .apply(setup_theta_sum_split_xor_vec[i * PART_SIZE + j][k]),
                        );
                    }

                    let mut tmp_theta_sum_split: ASTExpr<F>;
                    if v % 3 == 0 {
                        let st = v / 3;
                        if st != 0 {
                            tmp_theta_sum_split =
                                setup_theta_sum_split_vec[i * PART_SIZE + j][st - 1] * 1;
                            for k in 1..st {
                                tmp_theta_sum_split = tmp_theta_sum_split * 512
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j][st - k - 1];
                            }
                            tmp_theta_sum_split = tmp_theta_sum_split * 8
                                + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                    [NUM_PER_WORD_BATCH3 - 1];
                            for k in 1..NUM_PER_WORD_BATCH3 - st {
                                tmp_theta_sum_split = tmp_theta_sum_split * 512
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - k - 1];
                            }
                        } else {
                            tmp_theta_sum_split = setup_theta_sum_split_vec[i * PART_SIZE + j]
                                [NUM_PER_WORD_BATCH3 - 1]
                                * 1;
                            for k in 1..NUM_PER_WORD_BATCH3 {
                                tmp_theta_sum_split = tmp_theta_sum_split * 512
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - k - 1];
                            }
                        }
                    } else if v % 3 == 1 {
                        let st = (v - 1) / 3;
                        tmp_theta_sum_split = setup_rho_bit_1[i * PART_SIZE + j] * 1;
                        for k in 0..st {
                            tmp_theta_sum_split = tmp_theta_sum_split * 512
                                + setup_theta_sum_split_vec[i * PART_SIZE + j][st - k - 1];
                        }
                        for k in 0..NUM_PER_WORD_BATCH3 - st - 1 {
                            if k == 0 {
                                tmp_theta_sum_split = tmp_theta_sum_split * 8
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - 1];
                            } else {
                                tmp_theta_sum_split = tmp_theta_sum_split * 512
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - k - 1];
                            }
                        }
                        tmp_theta_sum_split =
                            tmp_theta_sum_split * 64 + setup_rho_bit_0[i * PART_SIZE + j];
                        ctx.constr(eq(
                            setup_rho_bit_0[i * PART_SIZE + j] * 8
                                + setup_rho_bit_1[i * PART_SIZE + j],
                            setup_theta_sum_split_vec[i * PART_SIZE + j][st],
                        ));
                    } else {
                        let st = (v - 2) / 3;
                        tmp_theta_sum_split = setup_rho_bit_1[i * PART_SIZE + j] * 1;
                        for k in 0..st {
                            tmp_theta_sum_split = tmp_theta_sum_split * 512
                                + setup_theta_sum_split_vec[i * PART_SIZE + j][st - k - 1];
                        }
                        for k in 0..NUM_PER_WORD_BATCH3 - st - 1 {
                            if k == 0 {
                                tmp_theta_sum_split = tmp_theta_sum_split * 8
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - 1];
                            } else {
                                tmp_theta_sum_split = tmp_theta_sum_split * 512
                                    + setup_theta_sum_split_vec[i * PART_SIZE + j]
                                        [NUM_PER_WORD_BATCH3 - k - 1];
                            }
                        }
                        tmp_theta_sum_split =
                            tmp_theta_sum_split * 8 + setup_rho_bit_0[i * PART_SIZE + j];
                        ctx.constr(eq(
                            setup_rho_bit_0[i * PART_SIZE + j] * 64
                                + setup_rho_bit_1[i * PART_SIZE + j],
                            setup_theta_sum_split_vec[i * PART_SIZE + j][st],
                        ));
                    }

                    ctx.constr(eq(
                        tmp_theta_sum_split,
                        setup_s_vec[i * PART_SIZE + j]
                            + tmp_theta_sum_split_xor_vec[(i + PART_SIZE - 1) % PART_SIZE].clone()
                            + tmp_theta_sum_move_split_xor_vec[(i + 1) % PART_SIZE].clone(),
                    ));
                }
            }

            let mut tmp_pi_sum_split_xor_vec = setup_theta_sum_split_xor_vec.clone();
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    tmp_pi_sum_split_xor_vec[j * PART_SIZE + ((2 * i + 3 * j) % PART_SIZE)] =
                        setup_theta_sum_split_xor_vec[i * PART_SIZE + j].clone();
                }
            }

            // chi
            // a[x] = a[x] ^ (~a[x+1] & a[x+2])
            // chi(3 - 2a[x] + a[x+1] - a[x+2])
            ctx.add_lookup(param.constants_table.apply(round).apply(round_cst));
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    for k in 0..NUM_PER_WORD_BATCH3 {
                        ctx.add_lookup(
                            param
                                .chi_table
                                .apply(
                                    tmp_pi_sum_split_xor_vec[((i + 1) % PART_SIZE) * PART_SIZE + j]
                                        [k]
                                        - tmp_pi_sum_split_xor_vec[i * PART_SIZE + j][k]
                                        - tmp_pi_sum_split_xor_vec[i * PART_SIZE + j][k]
                                        - tmp_pi_sum_split_xor_vec
                                            [((i + 2) % PART_SIZE) * PART_SIZE + j][k]
                                        + 219,
                                )
                                .apply(setup_chi_split_value_vec[i * PART_SIZE + j][k]),
                        );
                    }

                    let mut tmp_sum_split_chi_vec: ASTExpr<F> =
                        setup_chi_split_value_vec[i * PART_SIZE + j][NUM_PER_WORD_BATCH3 - 1] * 1;
                    for k in 1..NUM_PER_WORD_BATCH3 {
                        tmp_sum_split_chi_vec = tmp_sum_split_chi_vec * 512
                            + setup_chi_split_value_vec[i * PART_SIZE + j]
                                [NUM_PER_WORD_BATCH3 - k - 1];
                    }

                    if i != 0 || j != 0 {
                        ctx.transition(eq(
                            tmp_sum_split_chi_vec,
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));
                    } else {
                        let mut tmp_sum_s_split_vec: ASTExpr<F> =
                            setup_final_sum_split_vec[NUM_PER_WORD_BATCH4 - 1] * 1;
                        let mut tmp_sum_s_split_xor_vec: ASTExpr<F> =
                            setup_final_xor_split_vec[NUM_PER_WORD_BATCH4 - 1] * 1;
                        ctx.add_lookup(
                            param
                                .xor_table_batch4
                                .apply(setup_final_sum_split_vec[NUM_PER_WORD_BATCH4 - 1])
                                .apply(setup_final_xor_split_vec[NUM_PER_WORD_BATCH4 - 1]),
                        );
                        for (&value, &xor_value) in setup_final_sum_split_vec
                            .iter()
                            .zip(setup_final_xor_split_vec.iter())
                            .rev()
                            .take(NUM_PER_WORD_BATCH4)
                            .skip(1)
                        {
                            tmp_sum_s_split_vec = tmp_sum_s_split_vec * 64 * 64 + value;
                            tmp_sum_s_split_xor_vec = tmp_sum_s_split_xor_vec * 64 * 64 + xor_value;
                            ctx.add_lookup(param.xor_table_batch4.apply(value).apply(xor_value));
                        }

                        ctx.constr(eq(tmp_sum_s_split_vec, tmp_sum_split_chi_vec + round_cst));
                        ctx.transition(eq(
                            tmp_sum_s_split_xor_vec,
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));
                    }
                }
            }

            ctx.transition(eq((round + 1 - round.next()) * (round + 1 - NUM_ROUNDS), 0));
            ctx.transition(eq((round + 1 - round.next()) * round.next(), 0));
        });

        ctx.wg::<OneRoundValues<F>, _>(move |ctx, values| {
            ctx.assign(round, values.round);
            ctx.assign(round_cst, values.round_cst);

            for (q, v) in s_vec.iter().zip(values.s_vec.iter()) {
                ctx.assign(*q, *v)
            }
            for (q_vec, v_vec) in theta_split_vec.iter().zip(values.theta_split_vec.iter()) {
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
        })
    });
    let keccak_squeeze_step = ctx.step_type_def("keccak squeezing", |ctx| {
        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        let squeeze_split_vec: Vec<Vec<Queriable<F>>> = (0..SQUEEZE_VECTOR_NUM)
            .map(|i| {
                (0..SQUEEZE_SPLIT_NUM / 2)
                    .map(|j| ctx.internal(&format!("squeeze_split_vec_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_squeeze_split_vec = squeeze_split_vec.clone();

        let squeeze_split_output_vec: Vec<Vec<Queriable<F>>> = (0..SQUEEZE_VECTOR_NUM)
            .map(|i| {
                (0..SQUEEZE_SPLIT_NUM / 2)
                    .map(|j| ctx.internal(&format!("squeeze_split_output_vec_{}_{}", i, j)))
                    .collect()
            })
            .collect();
        let setup_squeeze_split_output_vec = squeeze_split_output_vec.clone();

        ctx.setup(move |ctx| {
            for i in 0..SQUEEZE_VECTOR_NUM {
                let mut tmp_squeeze_split_sum =
                    setup_squeeze_split_vec[i][SQUEEZE_SPLIT_NUM / 2 - 1] * 1;
                for j in 1..SQUEEZE_SPLIT_NUM / 2 {
                    tmp_squeeze_split_sum = tmp_squeeze_split_sum * 4096 * 4096
                        + setup_squeeze_split_vec[i][SQUEEZE_SPLIT_NUM / 2 - j - 1];
                }
                ctx.constr(eq(tmp_squeeze_split_sum, setup_s_vec[i * PART_SIZE]));
                for j in 0..SQUEEZE_SPLIT_NUM / 2 {
                    ctx.add_lookup(
                        param
                            .pack_table
                            .apply(setup_squeeze_split_vec[i][j])
                            .apply(setup_squeeze_split_output_vec[i][j]),
                    );
                }
            }
        });

        ctx.wg::<SqueezeValues<F>, _>(move |ctx, values| {
            for (q, v) in s_vec.iter().zip(values.s_vec.iter()) {
                ctx.assign(*q, *v)
            }

            for (q_vec, v_vec) in squeeze_split_vec
                .iter()
                .zip(values.squeeze_split_vec.iter())
            {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }

            for (q_vec, v_vec) in squeeze_split_output_vec
                .iter()
                .zip(values.squeeze_split_output_vec.iter())
            {
                for (q, v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q, *v)
                }
            }
        })
    });
    // ctx.pragma_first_step(&keccak_pre_step);
    ctx.pragma_first_step(&keccak_first_step); // keccak_pre_step

    ctx.pragma_last_step(&keccak_squeeze_step);

    ctx.pragma_num_steps(param.step_num);

    ctx.trace(move |ctx, params| {
        let mut bits = params.bits;
        println!("intput bits(without padding) = {:?}", bits);
        // padding
        bits.push(1);
        while (bits.len() + 1) % RATE_IN_BITS != 0 {
            bits.push(0);
        }
        bits.push(1);
        println!("intput bits(with padding) = {:?}", bits);

        let mut s_new = [F::ZERO; PART_SIZE * PART_SIZE];

        // chunks
        let chunks = bits.chunks(RATE_IN_BITS);

        // absorb
        for (k, chunk) in chunks.enumerate() {
            let s: Vec<F> = s_new.to_vec();
            let absorbs: Vec<F> = (0..PART_SIZE * PART_SIZE)
                .map(|idx| {
                    let i = idx % PART_SIZE;
                    let j = idx / PART_SIZE;
                    let mut absorb = F::ZERO;
                    if idx < NUM_WORDS_TO_ABSORB {
                        absorb = pack(&chunk[idx * 64..(idx + 1) * 64]);
                        s_new[i * PART_SIZE + j] = field_xor(s[i * PART_SIZE + j], absorb);
                    } else {
                        s_new[i * PART_SIZE + j] = s[i * PART_SIZE + j];
                    }
                    absorb
                })
                .collect();

            let absorb_split_vec: Vec<Vec<F>> = (0..NUM_WORDS_TO_ABSORB)
                .map(|idx| {
                    let bits = chunk[idx * 64..(idx + 1) * 64].to_vec();
                    (0..SQUEEZE_SPLIT_NUM / 2)
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

            let absorb_split_input_vec = (0..NUM_WORDS_TO_ABSORB)
                .map(|idx| {
                    let bits = chunk[idx * 64..(idx + 1) * 64].to_vec();
                    (0..SQUEEZE_SPLIT_NUM / 2)
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

            if k == 0 {
                let values = PreValues {
                    s_vec: s,
                    absorb_rows: absorbs[0..NUM_WORDS_TO_ABSORB].to_vec(),
                    round_value: F::ZERO,
                    absorb_split_vec,
                    absorb_split_input_vec,
                    split_values: Vec::new(),
                };
                ctx.add(&keccak_first_step, values);
                // let split_values: Vec<Vec<(F, F)>> = (0..NUM_WORDS_TO_ABSORB)
                //     .map(|t| {
                //         let i = t % PART_SIZE;
                //         let j = t / PART_SIZE;
                //         let v = i * PART_SIZE + j;
                //         let (xor_rows, _, _) = eval_keccak_f_to_bit_vec::<F>(
                //             s[v] + absorbs[(v % PART_SIZE) * PART_SIZE + (v / PART_SIZE)],
                //             s_new[v],
                //         );
                //         xor_rows
                //     })
                //     .collect();

                // for k in 0..NUM_WORDS_TO_ABSORB {
                //     let mut sum_split_vec =  split_values[k][NUM_PER_WORD - 1].0;

                //     for &value in split_values[k]
                //         .iter()
                //         .rev()
                //         .take(NUM_PER_WORD)
                //         .skip(1)
                //     {
                //         sum_split_vec = sum_split_vec * F::from(64) + value.0;

                //     }
                //     println!("sum_split_vec = {:?}, setup_sum_split_value_vec = {:?}",
                // sum_split_vec, s[(k % PART_SIZE) * PART_SIZE + (k / PART_SIZE)]+ absorbs[k]);

                // }

                // let values = PreValues{s_vec: s, absorb_rows:
                // absorbs[0..NUM_WORDS_TO_ABSORB].to_vec(), split_values, absorb_split_vec,
                // absorb_split_input_vec, round_value: F::ZERO,};
                // ctx.add(&keccak_pre_step, values);
            } else {
                let split_values = (0..NUM_WORDS_TO_ABSORB)
                    .map(|t| {
                        let i = t % PART_SIZE;
                        let j = t / PART_SIZE;
                        let v = i * PART_SIZE + j;
                        let (xor_rows, _, _) = eval_keccak_f_to_bit_vec::<F>(
                            s[v] + absorbs[(v % PART_SIZE) * PART_SIZE + (v / PART_SIZE)],
                            s_new[v],
                        );
                        xor_rows
                    })
                    .collect();
                let values = PreValues {
                    s_vec: s,
                    absorb_rows: absorbs[0..NUM_WORDS_TO_ABSORB].to_vec(),
                    split_values,
                    absorb_split_vec,
                    absorb_split_input_vec,
                    round_value: F::ZERO,
                };
                ctx.add(&keccak_pre_step, values);
            }

            for (round, &cst) in ROUND_CST.iter().enumerate().take(NUM_ROUNDS) {
                let values = eval_keccak_f_one_round(round as u64, cst, s_new.to_vec());

                s_new = values.s_new_vec.clone().try_into().unwrap();
                ctx.add(&keccak_one_round, values.clone());
            }
        }

        // squeezing
        let mut squeeze_split_vec: Vec<Vec<F>> = Vec::new();
        let mut squeeze_split_output_vec = Vec::new();
        for i in 0..4 {
            let bits = convert_field_to_vec_bits(s_new[i * PART_SIZE]);

            squeeze_split_vec.push(
                (0..SQUEEZE_SPLIT_NUM / 2)
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
                (0..SQUEEZE_SPLIT_NUM / 2)
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

        let values = SqueezeValues {
            s_vec: s_new.to_vec(),
            squeeze_split_vec,
            squeeze_split_output_vec,
        };
        ctx.add(&keccak_squeeze_step, values);

        let output2: Vec<Vec<u8>> = (0..4)
            .map(|k| {
                pack_with_base::<F>(&convert_field_to_vec_bits(s_new[k * PART_SIZE]), 2)
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
    pub bits: Vec<u8>,
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
        let in_n = (input_len + 1 + RATE_IN_BITS) / RATE_IN_BITS;
        let step_num = in_n * (1 + NUM_ROUNDS) + 1;

        let single_config = config(SingleRowCellManager {}, LogNSelectorBuilder {});
        let (_, constants_table) = ctx.sub_circuit(
            single_config.clone(),
            keccak_round_constants_table,
            NUM_ROUNDS + 1,
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

        let maxwidth_config = config(MaxWidthCellManager::new(199, true), LogNSelectorBuilder {});
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
    let super_circuit = keccak_super_circuit::<Fr>(circuit_param.bits.len());
    let witness = super_circuit.get_mapping().generate(circuit_param);

    for wit_gen in witness.values() {
        let wit_gen = wit_gen.clone();

        let mut circuit = super_circuit.get_sub_circuits()[5].clone();
        circuit
            .columns
            .append(&mut super_circuit.get_sub_circuits()[0].columns);
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
        plaf.set_challange_alias(0, "r_keccak".to_string());
        let wit = plaf_wit_gen.generate(Some(wit_gen));
        write_files("keccak3", &plaf, &wit).unwrap();
    }
}

fn keccak_run(circuit_param: KeccakCircuit, k: u32) {
    let super_circuit = keccak_super_circuit::<Fr>(circuit_param.bits.len());
    let compiled = chiquitoSuperCircuit2Halo2(&super_circuit);

    let circuit = ChiquitoHalo2SuperCircuit::new(
        compiled,
        super_circuit.get_mapping().generate(circuit_param),
    );

    let prover = MockProver::<Fr>::run(k, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

fn main() {
    let circuit_param = KeccakCircuit {
        bits: vec![
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
            0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1,
            1, 0, 0, 0, 0, 0,
        ],
    };

    keccak_run(circuit_param, 9);

    keccak_plaf(
        KeccakCircuit {
            bits: vec![
                0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
                0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
                1, 1, 1, 0, 0, 0, 0, 0,
            ],
        },
        9,
    );
}
