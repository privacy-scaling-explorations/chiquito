use chiquito::{
    frontend::dsl::{
        cb::{eq, select, table},
        lb::LookupTable,
        super_circuit, CircuitContext, StepTypeSetupContext, StepTypeWGHandler,
    },
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
use halo2_proofs::{
    dev::MockProver,
    halo2curves::{bn256::Fr, group::ff::PrimeField},
};
use std::{fmt::Write, hash::Hash};

pub const IV_LEN: usize = 8;
pub const SIGMA_VECTOR_LENGTH: usize = 16;
pub const SIGMA_VECTOR_NUMBER: usize = 10;
pub const R1: u64 = 32;
pub const R2: u64 = 24;
pub const R3: u64 = 16;
pub const R4: u64 = 63;
pub const MIXING_ROUNDS: u64 = 12;
pub const SPLIT_64BITS: u64 = 16;
pub const BASE_4BITS: u64 = 16;
pub const XOR_4SPLIT_64BITS: u64 = SPLIT_64BITS * SPLIT_64BITS;
pub const V_LEN: usize = 16;
pub const M_LEN: usize = 16;
pub const H_LEN: usize = 8;
pub const G_ROUNDS: u64 = 16;

pub const IV_VALUES: [u64; IV_LEN] = [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179,
];

pub const SIGMA_VALUES: [[usize; SIGMA_VECTOR_LENGTH]; SIGMA_VECTOR_NUMBER] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

pub const XOR_VALUES: [u8; XOR_4SPLIT_64BITS as usize] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13,
    12, 15, 14, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 3, 2, 1, 0, 7, 6, 5, 4, 11,
    10, 9, 8, 15, 14, 13, 12, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 5, 4, 7, 6, 1,
    0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 6, 7, 4, 5, 2, 3, 0, 1, 14, 15, 12, 13, 10, 11, 8, 9, 7,
    6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4,
    5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 2,
    3, 0, 1, 6, 7, 4, 5, 11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4, 12, 13, 14, 15, 8,
    9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 14,
    15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3,
    2, 1, 0,
];

pub fn string_to_u64(inputs: [&str; 4]) -> [u64; 4] {
    inputs
        .iter()
        .map(|&input| {
            assert_eq!(16, input.len());
            u64::from_le_bytes(
                (0..input.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&input[i..i + 2], 16).unwrap())
                    .collect::<Vec<u8>>()
                    .try_into()
                    .unwrap(),
            )
        })
        .collect::<Vec<u64>>()
        .try_into()
        .unwrap()
}

pub fn u64_to_string(inputs: &[u64; 4]) -> [String; 4] {
    inputs
        .iter()
        .map(|input| {
            let mut s = String::new();
            for byte in input.to_le_bytes() {
                write!(&mut s, "{:02x}", byte).expect("Unable to write");
            }
            s
        })
        .collect::<Vec<String>>()
        .try_into()
        .unwrap()
}

pub fn split_to_4bits_values<F: PrimeField + Hash>(vec_values: &[u64]) -> Vec<Vec<F>> {
    vec_values
        .iter()
        .map(|&value| {
            let mut value = value;
            (0..SPLIT_64BITS)
                .map(|_| {
                    let v = value % BASE_4BITS;
                    value >>= 4;
                    F::from(v)
                })
                .collect()
        })
        .collect()
}

fn blake2f_iv_table<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    let lookup_iv_row: Queriable<F> = ctx.fixed("iv row");
    let lookup_iv_value: Queriable<F> = ctx.fixed("iv value");

    let iv_values = IV_VALUES;
    ctx.pragma_num_steps(IV_LEN);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in iv_values.iter().enumerate() {
            ctx.assign(i, lookup_iv_row, F::from(i as u64));
            ctx.assign(i, lookup_iv_value, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_iv_row).add(lookup_iv_value))
}

// For range checking
fn blake2f_4bits_table<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    let lookup_4bits_row: Queriable<F> = ctx.fixed("4bits row");
    let lookup_4bits_value: Queriable<F> = ctx.fixed("4bits value");

    ctx.pragma_num_steps(SPLIT_64BITS as usize);
    ctx.fixed_gen(move |ctx| {
        for i in 0..SPLIT_64BITS as usize {
            ctx.assign(i, lookup_4bits_row, F::ONE);
            ctx.assign(i, lookup_4bits_value, F::from(i as u64));
        }
    });

    ctx.new_table(table().add(lookup_4bits_row).add(lookup_4bits_value))
}

fn blake2f_xor_4bits_table<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    let lookup_xor_row: Queriable<F> = ctx.fixed("xor row");
    let lookup_xor_value: Queriable<F> = ctx.fixed("xor value");

    ctx.pragma_num_steps((SPLIT_64BITS * SPLIT_64BITS) as usize);
    let xor_values = XOR_VALUES;
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in xor_values.iter().enumerate() {
            ctx.assign(i, lookup_xor_row, F::from(i as u64));
            ctx.assign(i, lookup_xor_value, F::from(value as u64));
        }
    });

    ctx.new_table(table().add(lookup_xor_row).add(lookup_xor_value))
}

#[derive(Clone, Copy)]
struct CircuitParams {
    pub iv_table: LookupTable,
    pub bits_table: LookupTable,
    pub xor_4bits_table: LookupTable,
}

impl CircuitParams {
    fn check_4bit<F: PrimeField + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        bits: Queriable<F>,
    ) {
        ctx.add_lookup(self.bits_table.apply(1).apply(bits));
    }

    fn check_3bit<F: PrimeField + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        bits: Queriable<F>,
    ) {
        ctx.add_lookup(self.bits_table.apply(1).apply(bits));
        ctx.add_lookup(self.bits_table.apply(1).apply(bits * 2));
    }

    fn check_xor<F: PrimeField + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        b1: Queriable<F>,
        b2: Queriable<F>,
        xor: Queriable<F>,
    ) {
        ctx.add_lookup(self.xor_4bits_table.apply(b1 * BASE_4BITS + b2).apply(xor));
    }

    fn check_not<F: PrimeField + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        b1: Queriable<F>,
        xor: Queriable<F>,
    ) {
        ctx.add_lookup(self.xor_4bits_table.apply(b1 * BASE_4BITS + 0xF).apply(xor));
    }

    fn check_iv<F: PrimeField + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        i: usize,
        iv: Queriable<F>,
    ) {
        ctx.add_lookup(self.iv_table.apply(i).apply(iv));
    }
}

struct PreInput<F> {
    round: F,
    t0: F,
    t1: F,
    f: F,
    v_vec: Vec<F>,
    h_vec: Vec<F>,
    m_vec: Vec<F>,
    h_split_4bits_vec: Vec<Vec<F>>,
    m_split_4bits_vec: Vec<Vec<F>>,
    t_split_4bits_vec: Vec<Vec<F>>,
    iv_split_4bits_vec: Vec<Vec<F>>,
    final_split_bits_vec: Vec<Vec<F>>,
}

struct GInput<F> {
    round: F,
    v_vec: Vec<F>,
    h_vec: Vec<F>,
    m_vec: Vec<F>,
    v_mid1_vec: Vec<F>,
    v_mid2_vec: Vec<F>,
    v_mid3_vec: Vec<F>,
    v_mid4_vec: Vec<F>,
    v_mid_va_bit_vec: Vec<Vec<F>>,
    v_mid_vb_bit_vec: Vec<Vec<F>>,
    v_mid_vc_bit_vec: Vec<Vec<F>>,
    v_mid_vd_bit_vec: Vec<Vec<F>>,
    v_xor_d_bit_vec: Vec<Vec<F>>,
    v_xor_b_bit_vec: Vec<Vec<F>>,
    b_bit_vec: Vec<F>,
    b_3bits_vec: Vec<F>,
}

struct FinalInput<F> {
    round: F,
    v_vec: Vec<F>,
    h_vec: Vec<F>,
    output_vec: Vec<F>,
    v_split_bit_vec: Vec<Vec<F>>,
    h_split_bit_vec: Vec<Vec<F>>,
    v_xor_split_bit_vec: Vec<Vec<F>>,
    final_split_bit_vec: Vec<Vec<F>>,
}

struct InputValues {
    pub round: u32,          // 32bit
    pub h_vec: [u64; H_LEN], // 8 * 64bits
    pub m_vec: [u64; M_LEN], // 16 * 64bits
    pub t0: u64,             // 64bits
    pub t1: u64,             // 64bits
    pub f: bool,             // 8bits
}

struct GStepParams<F> {
    m_vec: Vec<Queriable<F>>,
    v_mid_va_bit_vec: Vec<Queriable<F>>,
    v_mid_vb_bit_vec: Vec<Queriable<F>>,
    v_mid_vc_bit_vec: Vec<Queriable<F>>,
    v_mid_vd_bit_vec: Vec<Queriable<F>>,
    v_xor_b_bit_vec: Vec<Queriable<F>>,
    v_xor_d_bit_vec: Vec<Queriable<F>>,
    input_vec: Vec<Queriable<F>>,
    output_vec: Vec<Queriable<F>>,
    b_bit: Queriable<F>,
    b_3bits: Queriable<F>,
}

fn split_value_4bits<F: PrimeField + Hash>(mut value: u128, n: u64) -> Vec<F> {
    (0..n)
        .map(|_| {
            let v = value % BASE_4BITS as u128;
            value /= BASE_4BITS as u128;

            F::from(v as u64)
        })
        .collect()
}

fn split_xor_value<F: PrimeField + Hash>(value1: u64, value2: u64) -> Vec<F> {
    let mut value1 = value1;
    let mut value2 = value2;
    let bit_values: Vec<u64> = (0..64)
        .map(|_| {
            let b1 = value1 % 2;
            value1 /= 2;
            let b2 = value2 % 2;
            value2 /= 2;
            b1 ^ b2
        })
        .collect();
    (0..SPLIT_64BITS as usize)
        .map(|i| {
            F::from(
                bit_values[i * 4]
                    + bit_values[i * 4 + 1] * 2
                    + bit_values[i * 4 + 2] * 4
                    + bit_values[i * 4 + 3] * 8,
            )
        })
        .collect()
}

fn g_wg<F: PrimeField + Hash>(
    (v1_vec_values, v2_vec_values): (&mut [u64], &mut [u64]),
    (a, b, c, d): (usize, usize, usize, usize),
    (x, y): (u64, u64),
    (va_bit_vec, vb_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (vc_bit_vec, vd_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (v_xor_d_bit_vec, v_xor_b_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (b_bit_vec, b_3bits_vec): (&mut Vec<F>, &mut Vec<F>),
) {
    va_bit_vec.push(split_value_4bits(
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128,
        SPLIT_64BITS + 1,
    ));
    v1_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));
    v1_vec_values[d] = ((v1_vec_values[d] ^ v1_vec_values[a]) >> R1)
        ^ (v1_vec_values[d] ^ v1_vec_values[a]) << (64 - R1);
    v_xor_d_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));

    vc_bit_vec.push(split_value_4bits(
        v1_vec_values[c] as u128 + v1_vec_values[d] as u128,
        SPLIT_64BITS + 1,
    ));
    v1_vec_values[c] = (v1_vec_values[c] as u128 + v1_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));
    v1_vec_values[b] = ((v1_vec_values[b] ^ v1_vec_values[c]) >> R2)
        ^ (v1_vec_values[b] ^ v1_vec_values[c]) << (64 - R2);
    v_xor_b_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));

    va_bit_vec.push(split_value_4bits(
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128,
        SPLIT_64BITS + 1,
    ));
    v2_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));
    v2_vec_values[d] = ((v1_vec_values[d] ^ v2_vec_values[a]) >> R3)
        ^ (v1_vec_values[d] ^ v2_vec_values[a]) << (64 - R3);
    v_xor_d_bit_vec.push(split_value_4bits(v2_vec_values[d] as u128, SPLIT_64BITS));

    vc_bit_vec.push(split_value_4bits(
        v1_vec_values[c] as u128 + v2_vec_values[d] as u128,
        SPLIT_64BITS + 1,
    ));
    v2_vec_values[c] = (v1_vec_values[c] as u128 + v2_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));
    v2_vec_values[b] = ((v1_vec_values[b] ^ v2_vec_values[c]) >> R4)
        ^ (v1_vec_values[b] ^ v2_vec_values[c]) << (64 - R4);
    v_xor_b_bit_vec.push(split_value_4bits(
        (v1_vec_values[b] ^ v2_vec_values[c]) as u128,
        SPLIT_64BITS,
    ));
    let bits = (v1_vec_values[b] ^ v2_vec_values[c]) / 2u64.pow(60);
    b_bit_vec.push(F::from(bits / 8));
    b_3bits_vec.push(F::from(bits % 8))
}

fn split_4bit_signals<F: PrimeField + Hash>(
    ctx: &mut StepTypeSetupContext<F>,
    params: &CircuitParams,
    input: &[Queriable<F>],
    output: &[Vec<Queriable<F>>],
) {
    for (i, split_vec) in output.iter().enumerate() {
        let mut sum_value = 0.expr() * 1;

        for &bits in split_vec.iter().rev() {
            params.check_4bit(ctx, bits);
            sum_value = sum_value * BASE_4BITS + bits;
        }
        ctx.constr(eq(sum_value, input[i]))
    }
}

// We check G function one time by calling twice g_setup function.c
// Because the G function can be divided into two similar parts.
fn g_setup<F: PrimeField + Hash>(
    ctx: &mut StepTypeSetupContext<'_, F>,
    params: CircuitParams,
    q_params: GStepParams<F>,
    (a, b, c, d): (usize, usize, usize, usize),
    (move1, move2): (u64, u64),
    s: usize,
    flag: bool,
) {
    let mut a_bits_sum_value = 0.expr() * 1;
    let mut a_bits_sum_mod_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_mid_va_bit_vec.iter().rev().enumerate() {
        a_bits_sum_value = a_bits_sum_value * BASE_4BITS + bits;
        if j != 0 {
            a_bits_sum_mod_value = a_bits_sum_mod_value * BASE_4BITS + bits;
        }
        params.check_4bit(ctx, bits);
    }
    // check v_mid_va_bit_vec = 4bit split of v[a] + v[b] + x
    ctx.constr(eq(
        a_bits_sum_value,
        q_params.input_vec[a] + q_params.input_vec[b] + q_params.m_vec[s],
    ));
    // check v[a] = (v[a] + v[b] + x) mod 2^64
    ctx.constr(eq(a_bits_sum_mod_value, q_params.output_vec[a]));

    // check d_bits_sum_value = 4bit split of v[b]
    let mut d_bits_sum_value = 0.expr() * 1;
    for &bits in q_params.v_mid_vd_bit_vec.iter().rev() {
        d_bits_sum_value = d_bits_sum_value * BASE_4BITS + bits;
        params.check_4bit(ctx, bits);
    }
    ctx.constr(eq(d_bits_sum_value, q_params.input_vec[d]));

    let mut ad_xor_sum_value = 0.expr() * 1;
    for &bits in q_params.v_xor_d_bit_vec.iter().rev() {
        ad_xor_sum_value = ad_xor_sum_value * BASE_4BITS + bits;
    }
    // check v_xor_d_bit_vec =  4bit split of v[d]
    ctx.constr(eq(ad_xor_sum_value, q_params.output_vec[d]));
    // check v_xor_d_bit_vec[i] =  (v[d][i] ^ v[a][i]) >>> R1(or R3)
    for j in 0..SPLIT_64BITS as usize {
        params.check_xor(
            ctx,
            q_params.v_mid_va_bit_vec[j],
            q_params.v_mid_vd_bit_vec[j],
            q_params.v_xor_d_bit_vec
                [(j + BASE_4BITS as usize - move1 as usize) % BASE_4BITS as usize],
        );
    }

    // check v[c] = (v[c] + v[d]) mod 2^64
    let mut c_bits_sum_value = 0.expr() * 1;
    let mut c_bits_sum_mod_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_mid_vc_bit_vec.iter().rev().enumerate() {
        c_bits_sum_value = c_bits_sum_value * BASE_4BITS + bits;
        if j != 0 {
            c_bits_sum_mod_value = c_bits_sum_mod_value * BASE_4BITS + bits;
        }
        params.check_4bit(ctx, bits);
    }
    // check v_mid_vc_bit_vec = 4bit split of (v[c] + v[d])
    ctx.constr(eq(
        c_bits_sum_value,
        q_params.input_vec[c] + q_params.output_vec[d],
    ));
    // check v[c] =  (v[c] + v[d] ) mod 2^64
    ctx.constr(eq(c_bits_sum_mod_value, q_params.output_vec[c]));

    let mut b_bits_sum_value = 0.expr() * 1;
    for &bits in q_params.v_mid_vb_bit_vec.iter().rev() {
        b_bits_sum_value = b_bits_sum_value * BASE_4BITS + bits;
        params.check_4bit(ctx, bits);
    }

    // v_mid_vb_bit_vec = 4bit split of v[b]
    ctx.constr(eq(b_bits_sum_value, q_params.input_vec[b]));
    let mut bc_xor_sum_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_xor_b_bit_vec.iter().rev().enumerate() {
        if j == 0 && flag {
            // b_bit * 8 + b_3bits = v_xor_b_bit_vec[0]
            bc_xor_sum_value = q_params.b_3bits * 1;
            ctx.constr(eq(q_params.b_bit * 8 + q_params.b_3bits, bits));
        } else {
            bc_xor_sum_value = bc_xor_sum_value * BASE_4BITS + bits;
        }
        params.check_4bit(ctx, bits);
    }
    if flag {
        bc_xor_sum_value = bc_xor_sum_value * 2 + q_params.b_bit;

        ctx.constr(eq(q_params.b_bit * (q_params.b_bit - 1), 0));
        // To constraint b_3bits_vec[i/2] \in [0..8)
        params.check_3bit(ctx, q_params.b_3bits);
    }
    // check v_xor_b_bit_vec = v[b]
    ctx.constr(eq(bc_xor_sum_value, q_params.output_vec[b]));

    // check v_xor_b_bit_vec[i] =  (v[b][i] ^ v[c][i]) >>> R2(or R4)
    for j in 0..SPLIT_64BITS as usize {
        params.check_xor(
            ctx,
            q_params.v_mid_vb_bit_vec[j],
            q_params.v_mid_vc_bit_vec[j],
            q_params.v_xor_b_bit_vec
                [(j + BASE_4BITS as usize - move2 as usize) % BASE_4BITS as usize],
        );
    }
}

fn blake2f_circuit<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, InputValues>,
    params: CircuitParams,
) {
    let v_vec: Vec<Queriable<F>> = (0..V_LEN)
        .map(|i| ctx.forward(format!("v_vec[{}]", i).as_str()))
        .collect();
    let h_vec: Vec<Queriable<F>> = (0..H_LEN)
        .map(|i| ctx.forward(format!("h_vec[{}]", i).as_str()))
        .collect();
    let m_vec: Vec<Queriable<F>> = (0..M_LEN)
        .map(|i| ctx.forward(format!("m_vec[{}]", i).as_str()))
        .collect();
    let round = ctx.forward("round");

    let blake2f_pre_step = ctx.step_type_def("blake2f_pre_step", |ctx| {
        let v_vec = v_vec.clone();
        let wg_v_vec = v_vec.clone();

        let h_vec = h_vec.clone();
        let wg_h_vec = h_vec.clone();

        let m_vec = m_vec.clone();
        let wg_m_vec = m_vec.clone();

        let t0 = ctx.internal("t0");
        let t1 = ctx.internal("t1");
        let f = ctx.internal("f");

        // h_split_4bits_vec = 4bit split of h_vec
        let h_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("h_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_h_split_4bits_vec = h_split_4bits_vec.clone();

        // m_split_4bits_vec = 4bit split of m_vec
        let m_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..M_LEN)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("m_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_m_split_4bits_vec = m_split_4bits_vec.clone();

        // t_split_4bits_vec = 4bit split of t0 and t1
        let t_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..2)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("t_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_t_split_4bits_vec = t_split_4bits_vec.clone();

        // iv_split_4bits_vec = 4bit split of IV[5], IV[6], IV[7]
        let iv_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("iv_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_iv_split_4bits_vec = iv_split_4bits_vec.clone();

        // final_split_bits_vec = 4bit split of IV[5] xor t0, IV[6] xor t1, IV[7] xor
        // 0xFFFFFFFFFFFFFFFF,
        let final_split_bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("final_split_bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_final_split_bits_vec = final_split_bits_vec.clone();

        ctx.setup(move |ctx| {
            // check inputs: h_vec
            split_4bit_signals(ctx, &params, &h_vec, &h_split_4bits_vec);

            // check inputs: m_vec
            split_4bit_signals(ctx, &params, &m_vec, &m_split_4bits_vec);

            // check inputs: t0,t1
            split_4bit_signals(ctx, &params, &[t0, t1], &t_split_4bits_vec);

            // check input f
            ctx.constr(eq(f * (f - 1), 0));

            // check v_vec
            for i in 0..H_LEN {
                ctx.constr(eq(v_vec[i], h_vec[i]));
            }
            for (i, &iv) in v_vec[V_LEN / 2..V_LEN].iter().enumerate() {
                params.check_iv(ctx, i, iv);
            }

            // check the split-fields of v[12], v[13], v[14]
            split_4bit_signals(ctx, &params, &v_vec[12..15], &iv_split_4bits_vec);

            // check v[12] := v[12] ^ (t mod 2**w)
            // check v[13] := v[13] ^ (t >> w)
            for (i, (final_plit_bits_value, (iv_split_bits_value, t_split_bits_value))) in
                final_split_bits_vec
                    .iter()
                    .zip(iv_split_4bits_vec.iter().zip(t_split_4bits_vec.iter()))
                    .enumerate()
                    .take(2)
            {
                let mut final_bits_sum_value = 0.expr() * 1;
                for (&value, (&iv, &t)) in final_plit_bits_value.iter().rev().zip(
                    iv_split_bits_value
                        .iter()
                        .rev()
                        .zip(t_split_bits_value.iter().rev()),
                ) {
                    params.check_xor(ctx, iv, t, value);
                    final_bits_sum_value = final_bits_sum_value * BASE_4BITS + value;
                }
                ctx.constr(eq(final_bits_sum_value, v_vec[12 + i].next()))
            }

            // check if f, v[14] = v[14] ^ 0xffffffffffffffff else v[14]
            let mut final_bits_sum_value = 0.expr() * 1;
            for (&bits, &iv) in final_split_bits_vec[2]
                .iter()
                .rev()
                .zip(iv_split_4bits_vec[2].iter().rev())
            {
                params.check_not(ctx, iv, bits);
                final_bits_sum_value = final_bits_sum_value * BASE_4BITS + bits;
            }

            // check v_vec v_vec.next
            for &v in v_vec.iter().take(12) {
                ctx.transition(eq(v, v.next()));
            }
            ctx.transition(eq(
                select(f, final_bits_sum_value, v_vec[14]),
                v_vec[14].next(),
            ));
            ctx.transition(eq(v_vec[15], v_vec[15].next()));
            // check h_vec h_vec.next
            for &h in h_vec.iter() {
                ctx.transition(eq(h, h.next()));
            }
            // check m_vec m_vec.next
            for &m in m_vec.iter() {
                ctx.transition(eq(m, m.next()));
            }

            ctx.constr(eq(round, 0));
            ctx.transition(eq(round, round.next()));
        });

        ctx.wg(move |ctx, inputs: PreInput<F>| {
            ctx.assign(round, inputs.round);
            ctx.assign(t0, inputs.t0);
            ctx.assign(t1, inputs.t1);
            ctx.assign(f, inputs.f);
            for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in wg_m_vec.iter().zip(inputs.m_vec.iter()) {
                ctx.assign(q, v)
            }
            for (q_vec, v_vec) in wg_h_split_4bits_vec
                .iter()
                .zip(inputs.h_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_m_split_4bits_vec
                .iter()
                .zip(inputs.m_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_t_split_4bits_vec
                .iter()
                .zip(inputs.t_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_iv_split_4bits_vec
                .iter()
                .zip(inputs.iv_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_final_split_bits_vec
                .iter()
                .zip(inputs.final_split_bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
        })
    });

    let blake2f_g_setup_vec: Vec<StepTypeWGHandler<F, _, _>> = (0..MIXING_ROUNDS as usize)
        .map(|r| {
            ctx.step_type_def(format!("blake2f_g_setup_{}", r), |ctx| {
                let v_vec = v_vec.clone();
                let wg_v_vec = v_vec.clone();
                let h_vec = h_vec.clone();
                let wg_h_vec = h_vec.clone();
                let m_vec = m_vec.clone();
                let wg_m_vec = m_vec.clone();

                // v_mid1_vec is the new v_vec after the first round call to the g_setup function
                let v_mid1_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid1_vec[{}]", i).as_str()))
                    .collect();
                let wg_v_mid1_vec = v_mid1_vec.clone();

                // v_mid2_vec is the new v_vec after the second round call to the g_setup function
                let v_mid2_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid2_vec[{}]", i).as_str()))
                    .collect();
                let wg_v_mid2_vec = v_mid2_vec.clone();

                // v_mid3_vec is the new v_vec after the third round to the g_setup function
                let v_mid3_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid3_vec[{}]", i).as_str()))
                    .collect();
                let wg_v_mid3_vec = v_mid3_vec.clone();

                // v_mid4_vec is the new v_vec after the forth round to the g_setup function，as
                // well as the final result of v_vec
                let v_mid4_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid4_vec[{}]", i).as_str()))
                    .collect();
                let wg_v_mid4_vec = v_mid4_vec.clone();

                // v_mid_va_bit_vec = 4bit split of v[a] + v[b] + x(or y)
                let v_mid_va_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS + 1)
                            .map(|j| {
                                ctx.internal(format!("v_mid_va_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_mid_va_bit_vec = v_mid_va_bit_vec.clone();

                // v_mid_vd_bit_vec = 4bit split of v[d]
                let v_mid_vd_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vd_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_mid_vd_bit_vec = v_mid_vd_bit_vec.clone();

                // v_mid_vc_bit_vec = 4bit split of v[c] + v[d]
                let v_mid_vc_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS + 1)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vc_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_mid_vc_bit_vec = v_mid_vc_bit_vec.clone();

                // v_mid_vb_bit_vec = 4bit split of v[b]
                let v_mid_vb_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vb_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_mid_vb_bit_vec = v_mid_vb_bit_vec.clone();

                // v_xor_d_bit_vec = 4bit split of  (v[d] ^ v[a]) >>> R1(or R3)
                let v_xor_d_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS)
                            .map(|j| {
                                ctx.internal(format!("v_xor_d_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_xor_d_bit_vec = v_xor_d_bit_vec.clone();

                // v_xor_b_bit_vec = 4bit split of (v[b] ^ v[c]) >>> R2(or R4)
                let v_xor_b_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                    .map(|i| {
                        (0..SPLIT_64BITS)
                            .map(|j| {
                                ctx.internal(format!("v_xor_b_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let wg_v_xor_b_bit_vec = v_xor_b_bit_vec.clone();

                // b_bit_vec[i] * 8 + b_3bits_vec[i] = v_xor_b_bit_vec[i * 2 + 1][0]
                // the step of v[b] := (v[b] ^ v[c]) >>> R4 needs to split a 4-bit value to a
                // one-bit value and a 3-bit value
                let b_bit_vec: Vec<Queriable<F>> = (0..G_ROUNDS / 2)
                    .map(|i| ctx.internal(format!("b_bit_vec[{}]", i).as_str()))
                    .collect();
                let wg_b_bit_vec = b_bit_vec.clone();
                let b_3bits_vec: Vec<Queriable<F>> = (0..G_ROUNDS / 2)
                    .map(|i| ctx.internal(format!("b_3bits_vec[{}]", i).as_str()))
                    .collect();
                let wg_b_3bits_vec = b_3bits_vec.clone();

                ctx.setup(move |ctx| {
                    let s = SIGMA_VALUES[r % 10];

                    for i in 0..G_ROUNDS as usize {
                        let mut input_vec = v_vec.clone();
                        let mut output_vec = v_mid1_vec.clone();
                        if i >= 8 {
                            if i % 2 == 0 {
                                input_vec = v_mid2_vec.clone();
                                output_vec = v_mid3_vec.clone();
                            } else {
                                input_vec = v_mid3_vec.clone();
                                output_vec = v_mid4_vec.clone();
                            }
                        } else if i % 2 == 1 {
                            input_vec = v_mid1_vec.clone();
                            output_vec = v_mid2_vec.clone();
                        }
                        let (mut a, mut b, mut c, mut d) =
                            (i / 2, 4 + i / 2, 8 + i / 2, 12 + i / 2);
                        if i / 2 == 4 {
                            (a, b, c, d) = (0, 5, 10, 15);
                        } else if i / 2 == 5 {
                            (a, b, c, d) = (1, 6, 11, 12);
                        } else if i / 2 == 6 {
                            (a, b, c, d) = (2, 7, 8, 13);
                        } else if i / 2 == 7 {
                            (a, b, c, d) = (3, 4, 9, 14);
                        }
                        let mut move1 = R1 / 4;
                        let mut move2 = R2 / 4;
                        if i % 2 == 1 {
                            move1 = R3 / 4;
                            move2 = (R4 + 1) / 4;
                        }
                        let q_params = GStepParams {
                            input_vec,
                            output_vec,
                            m_vec: m_vec.clone(),
                            v_mid_va_bit_vec: v_mid_va_bit_vec[i].clone(),
                            v_mid_vb_bit_vec: v_mid_vb_bit_vec[i].clone(),
                            v_mid_vc_bit_vec: v_mid_vc_bit_vec[i].clone(),
                            v_mid_vd_bit_vec: v_mid_vd_bit_vec[i].clone(),
                            v_xor_b_bit_vec: v_xor_b_bit_vec[i].clone(),
                            v_xor_d_bit_vec: v_xor_d_bit_vec[i].clone(),
                            b_bit: b_bit_vec[i / 2],
                            b_3bits: b_3bits_vec[i / 2],
                        };
                        g_setup(
                            ctx,
                            params,
                            q_params,
                            (a, b, c, d),
                            (move1, move2),
                            s[i],
                            i % 2 == 1,
                        );
                    }

                    // check v_vec v_vec.next()
                    for (&v, &new_v) in v_vec.iter().zip(v_mid4_vec.iter()) {
                        ctx.transition(eq(new_v, v.next()));
                    }
                    // check h_vec h_vec.next()
                    for &h in h_vec.iter() {
                        ctx.transition(eq(h, h.next()));
                    }
                    // check m_vec m_vec.next()
                    if r < MIXING_ROUNDS as usize - 1 {
                        for &m in m_vec.iter() {
                            ctx.transition(eq(m, m.next()));
                        }
                    }
                    ctx.transition(eq(round + 1, round.next()));
                });

                ctx.wg(move |ctx, inputs: GInput<F>| {
                    ctx.assign(round, inputs.round);
                    for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_m_vec.iter().zip(inputs.m_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_v_mid1_vec.iter().zip(inputs.v_mid1_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_v_mid2_vec.iter().zip(inputs.v_mid2_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_v_mid3_vec.iter().zip(inputs.v_mid3_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_v_mid4_vec.iter().zip(inputs.v_mid4_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (q_vec, v_vec) in wg_v_mid_va_bit_vec
                        .iter()
                        .zip(inputs.v_mid_va_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in wg_v_mid_vb_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vb_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in wg_v_mid_vc_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vc_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in wg_v_mid_vd_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vd_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in
                        wg_v_xor_d_bit_vec.iter().zip(inputs.v_xor_d_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in
                        wg_v_xor_b_bit_vec.iter().zip(inputs.v_xor_b_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (&q, &v) in wg_b_bit_vec.iter().zip(inputs.b_bit_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in wg_b_3bits_vec.iter().zip(inputs.b_3bits_vec.iter()) {
                        ctx.assign(q, v)
                    }
                })
            })
        })
        .collect();

    let blake2f_final_step = ctx.step_type_def("blake2f_final_step", |ctx| {
        let v_vec = v_vec.clone();
        let wg_v_vec = v_vec.clone();

        let h_vec = h_vec.clone();
        let wg_h_vec = h_vec.clone();

        let output_vec = m_vec.clone();
        let wg_output_vec = output_vec.clone();

        // v_split_bit_vec = 4bit split of v_vec
        let v_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("v_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_v_split_bit_vec = v_split_bit_vec.clone();

        // h_split_bit_vec = 4bit split of h_vec
        let h_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("h_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_h_split_bit_vec = h_split_bit_vec.clone();

        // v_xor_split_bit_vec = 4bit split of v[i] ^ v[i + 8]
        let v_xor_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_v_xor_split_bit_vec = v_xor_split_bit_vec.clone();

        // final_split_bit_vec = 4bit split of h[i] ^ v[i] ^ v[i + 8]
        let final_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
            .map(|i| {
                (0..SPLIT_64BITS)
                    .map(|j| ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let wg_final_split_bit_vec = final_split_bit_vec.clone();

        ctx.setup(move |ctx| {
            // check split-fields of v_vec
            for (&v, v_split) in v_vec.iter().zip(v_split_bit_vec.iter()) {
                let mut v_4bits_sum_value = 0.expr() * 1;
                for &bits in v_split.iter().rev() {
                    v_4bits_sum_value = v_4bits_sum_value * BASE_4BITS + bits;
                    params.check_4bit(ctx, bits);
                }
                ctx.constr(eq(v_4bits_sum_value, v));
            }

            // check split-fields of h_vec
            for (&h, h_split) in h_vec.iter().zip(h_split_bit_vec.iter()) {
                let mut h_4bits_sum_value = 0.expr() * 1;
                for &bits in h_split.iter().rev() {
                    h_4bits_sum_value = h_4bits_sum_value * BASE_4BITS + bits;
                    params.check_4bit(ctx, bits);
                }
                ctx.constr(eq(h_4bits_sum_value, h));
            }

            // check split-fields of v[i] ^ v[i+8]
            for (xor_vec, (v1_vec, v2_vec)) in v_xor_split_bit_vec.iter().zip(
                v_split_bit_vec[0..V_LEN / 2]
                    .iter()
                    .zip(v_split_bit_vec[V_LEN / 2..V_LEN].iter()),
            ) {
                for (&xor, (&v1, &v2)) in xor_vec.iter().zip(v1_vec.iter().zip(v2_vec.iter())) {
                    params.check_xor(ctx, v1, v2, xor);
                }
            }

            // check split-fields of h[i] ^ v[i] ^ v[i+8]
            for (final_vec, (xor_vec, h_vec)) in final_split_bit_vec
                .iter()
                .zip(v_xor_split_bit_vec.iter().zip(h_split_bit_vec.iter()))
            {
                for (&value, (&v1, &v2)) in final_vec.iter().zip(xor_vec.iter().zip(h_vec.iter())) {
                    params.check_xor(ctx, v1, v2, value);
                }
            }

            // check output = h[i] ^ v[i] ^ v[i+8]
            for (final_vec, &output) in final_split_bit_vec.iter().zip(output_vec.iter()) {
                let mut final_4bits_sum_value = 0.expr() * 1;
                for &value in final_vec.iter().rev() {
                    final_4bits_sum_value = final_4bits_sum_value * BASE_4BITS + value;
                }
                ctx.constr(eq(output, final_4bits_sum_value));
            }
            ctx.constr(eq(round, MIXING_ROUNDS));
        });

        ctx.wg(move |ctx, inputs: FinalInput<F>| {
            ctx.assign(round, inputs.round);
            for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in wg_output_vec.iter().zip(inputs.output_vec.iter()) {
                ctx.assign(q, v)
            }
            for (q_vec, v_vec) in wg_v_split_bit_vec.iter().zip(inputs.v_split_bit_vec.iter()) {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_h_split_bit_vec.iter().zip(inputs.h_split_bit_vec.iter()) {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_v_xor_split_bit_vec
                .iter()
                .zip(inputs.v_xor_split_bit_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in wg_final_split_bit_vec
                .iter()
                .zip(inputs.final_split_bit_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
        })
    });

    ctx.pragma_first_step(&blake2f_pre_step);
    ctx.pragma_last_step(&blake2f_final_step);
    ctx.pragma_num_steps(MIXING_ROUNDS as usize + 2);

    ctx.trace(move |ctx, values| {
        let h_vec_values = values.h_vec.to_vec();
        let h_split_4bits_vec = split_to_4bits_values::<F>(&h_vec_values);

        let m_vec_values = values.m_vec.to_vec();
        let m_split_4bits_vec = split_to_4bits_values::<F>(&m_vec_values);

        let mut iv_vec_values = IV_VALUES.to_vec();
        let iv_split_4bits_vec: Vec<Vec<F>> = split_to_4bits_values::<F>(&iv_vec_values[4..7]);

        let mut v_vec_values = h_vec_values.clone();
        v_vec_values.append(&mut iv_vec_values);

        let t_split_4bits_vec = split_to_4bits_values::<F>(&[values.t0, values.t1]);

        let final_values = vec![
            v_vec_values[12] ^ values.t0,
            v_vec_values[13] ^ values.t1,
            v_vec_values[14] ^ 0xFFFFFFFFFFFFFFFF,
        ];
        let final_split_bits_vec = split_to_4bits_values::<F>(&final_values);

        let pre_inputs = PreInput {
            round: F::ZERO,
            t0: F::from(values.t0),
            t1: F::from(values.t1),
            f: F::from(if values.f { 1 } else { 0 }),
            h_vec: h_vec_values.iter().map(|&v| F::from(v)).collect(),
            m_vec: m_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_vec: v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_split_4bits_vec,
            m_split_4bits_vec,
            t_split_4bits_vec,
            iv_split_4bits_vec,
            final_split_bits_vec,
        };
        ctx.add(&blake2f_pre_step, pre_inputs);

        v_vec_values[12] = final_values[0];
        v_vec_values[13] = final_values[1];
        if values.f {
            v_vec_values[14] = final_values[2];
        }

        for r in 0..values.round {
            let s = SIGMA_VALUES[(r as usize) % 10];

            let mut v_mid1_vec_values = v_vec_values.clone();
            let mut v_mid2_vec_values = v_vec_values.clone();
            let mut v_mid_va_bit_vec = Vec::new();
            let mut v_mid_vb_bit_vec = Vec::new();
            let mut v_mid_vc_bit_vec = Vec::new();
            let mut v_mid_vd_bit_vec = Vec::new();
            let mut v_xor_d_bit_vec = Vec::new();
            let mut v_xor_b_bit_vec = Vec::new();
            let mut b_bit_vec = Vec::new();
            let mut b_3bits_vec = Vec::new();

            g_wg(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (0, 4, 8, 12),
                (m_vec_values[s[0]], m_vec_values[s[1]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (1, 5, 9, 13),
                (m_vec_values[s[2]], m_vec_values[s[3]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (2, 6, 10, 14),
                (m_vec_values[s[4]], m_vec_values[s[5]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (3, 7, 11, 15),
                (m_vec_values[s[6]], m_vec_values[s[7]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );

            let mut v_mid3_vec_values = v_mid2_vec_values.clone();
            let mut v_mid4_vec_values = v_mid2_vec_values.clone();
            g_wg(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (0, 5, 10, 15),
                (m_vec_values[s[8]], m_vec_values[s[9]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (1, 6, 11, 12),
                (m_vec_values[s[10]], m_vec_values[s[11]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (2, 7, 8, 13),
                (m_vec_values[s[12]], m_vec_values[s[13]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_wg(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (3, 4, 9, 14),
                (m_vec_values[s[14]], m_vec_values[s[15]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );

            let ginputs = GInput {
                round: F::from(r as u64),
                v_vec: v_vec_values.iter().map(|&v| F::from(v)).collect(),
                h_vec: h_vec_values.iter().map(|&v| F::from(v)).collect(),
                m_vec: m_vec_values.iter().map(|&v| F::from(v)).collect(),
                v_mid1_vec: v_mid1_vec_values.iter().map(|&v| F::from(v)).collect(),
                v_mid2_vec: v_mid2_vec_values.iter().map(|&v| F::from(v)).collect(),
                v_mid3_vec: v_mid3_vec_values.iter().map(|&v| F::from(v)).collect(),
                v_mid4_vec: v_mid4_vec_values.iter().map(|&v| F::from(v)).collect(),
                v_mid_va_bit_vec,
                v_mid_vb_bit_vec,
                v_mid_vc_bit_vec,
                v_mid_vd_bit_vec,
                v_xor_d_bit_vec,
                v_xor_b_bit_vec,
                b_bit_vec,
                b_3bits_vec,
            };
            ctx.add(&blake2f_g_setup_vec[r as usize], ginputs);
            v_vec_values = v_mid4_vec_values.clone();
        }

        let output_vec_values: Vec<u64> = h_vec_values
            .iter()
            .zip(
                v_vec_values[0..8]
                    .iter()
                    .zip(v_vec_values[V_LEN / 2..V_LEN].iter()),
            )
            .map(|(h, (v1, v2))| h ^ v1 ^ v2)
            .collect();

        let final_inputs = FinalInput {
            round: F::from(values.round as u64),
            v_vec: v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_vec: h_vec_values.iter().map(|&v| F::from(v)).collect(),
            output_vec: output_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_split_bit_vec: v_vec_values
                .iter()
                .map(|&v| split_value_4bits(v as u128, SPLIT_64BITS))
                .collect(),
            h_split_bit_vec: h_vec_values
                .iter()
                .map(|&v| split_value_4bits(v as u128, SPLIT_64BITS))
                .collect(),
            v_xor_split_bit_vec: v_vec_values[0..V_LEN / 2]
                .iter()
                .zip(v_vec_values[V_LEN / 2..V_LEN].iter())
                .map(|(&v1, &v2)| split_xor_value(v1, v2))
                .collect(),
            final_split_bit_vec: output_vec_values
                .iter()
                .map(|&output| split_value_4bits(output as u128, SPLIT_64BITS))
                .collect(),
        };
        ctx.add(&blake2f_final_step, final_inputs);
        // ba80a53f981c4d0d, 6a2797b69f12f6e9, 4c212f14685ac4b7, 4b12bb6fdbffa2d1
        // 7d87c5392aab792d, c252d5de4533cc95, 18d38aa8dbf1925a,b92386edd4009923
        println!(
            "output = {:?} \n         {:?}",
            u64_to_string(&output_vec_values[0..4].try_into().unwrap()),
            u64_to_string(&output_vec_values[4..8].try_into().unwrap())
        );
    })
}

fn blake2f_super_circuit<F: PrimeField + Hash>() -> SuperCircuit<F, InputValues> {
    super_circuit::<F, InputValues, _>("blake2f", |ctx| {
        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        let (_, iv_table) = ctx.sub_circuit(single_config.clone(), blake2f_iv_table, IV_LEN);
        let (_, bits_table) = ctx.sub_circuit(
            single_config.clone(),
            blake2f_4bits_table,
            SPLIT_64BITS as usize,
        );
        let (_, xor_4bits_table) = ctx.sub_circuit(
            single_config,
            blake2f_xor_4bits_table,
            (SPLIT_64BITS * SPLIT_64BITS) as usize,
        );

        let maxwidth_config = config(
            MaxWidthCellManager::new(250, true),
            SimpleStepSelectorBuilder {},
        );

        let params = CircuitParams {
            iv_table,
            bits_table,
            xor_4bits_table,
        };
        let (blake2f, _) = ctx.sub_circuit(maxwidth_config, blake2f_circuit, params);

        ctx.mapping(move |ctx, values| {
            ctx.map(&blake2f, values);
        })
    })
}

fn main() {
    let super_circuit = blake2f_super_circuit::<Fr>();
    let compiled = chiquitoSuperCircuit2Halo2(&super_circuit);

    // h[0] = hex"48c9bdf267e6096a 3ba7ca8485ae67bb 2bf894fe72f36e3c f1361d5f3af54fa5";
    // h[1] = hex"d182e6ad7f520e51 1f6c3e2b8c68059b 6bbd41fbabd9831f 79217e1319cde05b";
    let h0 = string_to_u64([
        "48c9bdf267e6096a",
        "3ba7ca8485ae67bb",
        "2bf894fe72f36e3c",
        "f1361d5f3af54fa5",
    ]);
    let h1 = string_to_u64([
        "d182e6ad7f520e51",
        "1f6c3e2b8c68059b",
        "6bbd41fbabd9831f",
        "79217e1319cde05b",
    ]);
    // m[0] = hex"6162630000000000 0000000000000000 0000000000000000 0000000000000000";
    // m[1] = hex"0000000000000000 0000000000000000 0000000000000000 0000000000000000";
    // m[2] = hex"0000000000000000 0000000000000000 0000000000000000 0000000000000000";
    // m[3] = hex"0000000000000000 0000000000000000 0000000000000000 0000000000000000";
    let m0 = string_to_u64([
        "6162630000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
    ]);
    let m1 = string_to_u64([
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
    ]);
    let m2 = string_to_u64([
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
    ]);
    let m3 = string_to_u64([
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
    ]);

    let values = InputValues {
        round: 12,

        h_vec: [
            h0[0], // 0x6a09e667f2bdc948,
            h0[1], // 0xbb67ae8584caa73b,
            h0[2], // 0x3c6ef372fe94f82b,
            h0[3], // 0xa54ff53a5f1d36f1,
            h1[0], // 0x510e527fade682d1,
            h1[1], // 0x9b05688c2b3e6c1f,
            h1[2], // 0x1f83d9abfb41bd6b,
            h1[3], // 0x5be0cd19137e2179,
        ], // 8 * 64bits

        m_vec: [
            m0[0], // 0x636261,
            m0[1], // 0,
            m0[2], // 0,
            m0[3], // 0,
            m1[0], // 0,
            m1[1], // 0,
            m1[2], // 0,
            m1[3], // 0,
            m2[0], // 0,
            m2[1], // 0,
            m2[2], // 0,
            m2[3], // 0,
            m3[0], // 0,
            m3[1], // 0,
            m3[2], // 0,
            m3[3], // 0,
        ], // 16 * 64bits
        t0: 3,   // 64bits
        t1: 0,   // 64bits
        f: true, // 8bits
    };

    let circuit =
        ChiquitoHalo2SuperCircuit::new(compiled, super_circuit.get_mapping().generate(values));

    let prover = MockProver::run(9, &circuit, Vec::new()).unwrap();
    let result = prover.verify();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}
