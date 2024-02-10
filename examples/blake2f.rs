use chiquito::{
    frontend::dsl::{
        cb::{eq, select, table},
        lb::LookupTable,
        super_circuit, CircuitContext, StepTypeWGHandler,
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
use std::hash::Hash;

pub const IV_LENGTH: usize = 8;
pub const SIGMA_VECTOR_LENGTH: usize = 16;
pub const R1: usize = 32;
pub const R2: usize = 24;
pub const R3: usize = 16;
pub const R4: usize = 63;
pub const MIXING_ROUND: usize = 12;
pub const BITS_NUMBER: usize = 16;
pub const VALUE_4BITS: u64 = 16;
pub const XOR_4BITS_NUMBER: usize = BITS_NUMBER * BITS_NUMBER;
pub const V_LEN: usize = 16;
pub const M_LEN: usize = 16;
pub const H_LEN: usize = 8;
pub const G_ROUND: usize = 16;

pub const IV_VALUES: [u64; IV_LENGTH] = [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179,
];

pub const SIGMA_VALUES: [[usize; SIGMA_VECTOR_LENGTH]; 10] = [
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

pub const XOR_VALUES: [u64; XOR_4BITS_NUMBER] = [
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

fn split_value_4bits<F: PrimeField + Hash>(value: u128, n: usize) -> (Vec<F>, F, F) {
    let mut value = value;
    let mut b_bit = F::ZERO;
    let mut b_3bits = F::ZERO;
    let result = (0..n)
        .map(|i| {
            let v = value % VALUE_4BITS as u128;
            value /= VALUE_4BITS as u128;
            if i == n - 1 {
                b_bit = F::from((v / 8) as u64);
                b_3bits = F::from((v % 8) as u64);
            }
            F::from(v as u64)
        })
        .collect();
    (result, b_bit, b_3bits)
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
    (0..BITS_NUMBER)
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

fn blake2f_iv_table<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    let lookup_iv_row: Queriable<F> = ctx.fixed("iv row");
    let lookup_iv_value: Queriable<F> = ctx.fixed("iv value");

    let iv_values = IV_VALUES;
    ctx.pragma_num_steps(IV_LENGTH);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in iv_values.iter().enumerate().take(IV_LENGTH) {
            ctx.assign(i, lookup_iv_row, F::from(i as u64));
            ctx.assign(i, lookup_iv_value, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_iv_row).add(lookup_iv_value))
}

fn blake2f_4bits_table<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    _: usize,
) -> LookupTable {
    let lookup_4bits_row: Queriable<F> = ctx.fixed("4bits row");
    let lookup_4bits_value: Queriable<F> = ctx.fixed("4bits value");

    ctx.pragma_num_steps(BITS_NUMBER);
    ctx.fixed_gen(move |ctx| {
        for i in 0..BITS_NUMBER {
            ctx.assign(i, lookup_4bits_row, F::from(i as u64));
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

    ctx.pragma_num_steps(BITS_NUMBER * BITS_NUMBER);
    let xor_values = XOR_VALUES;
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in xor_values
            .iter()
            .enumerate()
            .take(BITS_NUMBER * BITS_NUMBER)
        {
            ctx.assign(i, lookup_xor_row, F::from(i as u64));
            ctx.assign(i, lookup_xor_value, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_xor_row).add(lookup_xor_value))
}

struct CircuitParams {
    pub iv_table: LookupTable,
    pub bits_table: LookupTable,
    pub xor_4bits_table: LookupTable,
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

#[derive(Default)]
struct InputValues {
    pub round: u32,          // 32bit
    pub h_vec: [u64; H_LEN], // 8 * 64bits
    pub m_vec: [u64; M_LEN], // 16 * 64bits
    pub t0: u64,             // 64bits
    pub t1: u64,             // 64bits
    pub f: bool,             // 8bits
}

fn g_internal<F: PrimeField + Hash>(
    (v1_vec_values, v2_vec_values): (&mut [u64], &mut [u64]),
    (a, b, c, d): (usize, usize, usize, usize),
    (x, y): (u64, u64),
    (va_bit_vec, vb_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (vc_bit_vec, vd_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (v_xor_d_bit_vec, v_xor_b_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (b_bit_vec, b_3bits_vec): (&mut Vec<F>, &mut Vec<F>),
) {
    va_bit_vec.push(
        split_value_4bits(
            v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128,
            BITS_NUMBER + 1,
        )
        .0,
    );
    v1_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, BITS_NUMBER).0);
    v1_vec_values[d] = ((v1_vec_values[d] ^ v1_vec_values[a]) >> R1)
        ^ (v1_vec_values[d] ^ v1_vec_values[a]) << (64 - R1);
    v_xor_d_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, BITS_NUMBER).0);

    vc_bit_vec.push(
        split_value_4bits(
            v1_vec_values[c] as u128 + v1_vec_values[d] as u128,
            BITS_NUMBER + 1,
        )
        .0,
    );
    v1_vec_values[c] = (v1_vec_values[c] as u128 + v1_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, BITS_NUMBER).0);
    v1_vec_values[b] = ((v1_vec_values[b] ^ v1_vec_values[c]) >> R2)
        ^ (v1_vec_values[b] ^ v1_vec_values[c]) << (64 - R2);
    v_xor_b_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, BITS_NUMBER).0);

    va_bit_vec.push(
        split_value_4bits(
            v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128,
            BITS_NUMBER + 1,
        )
        .0,
    );
    v2_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, BITS_NUMBER).0);
    v2_vec_values[d] = ((v1_vec_values[d] ^ v2_vec_values[a]) >> R3)
        ^ (v1_vec_values[d] ^ v2_vec_values[a]) << (64 - R3);
    v_xor_d_bit_vec.push(split_value_4bits(v2_vec_values[d] as u128, BITS_NUMBER).0);

    vc_bit_vec.push(
        split_value_4bits(
            v1_vec_values[c] as u128 + v2_vec_values[d] as u128,
            BITS_NUMBER + 1,
        )
        .0,
    );
    v2_vec_values[c] = (v1_vec_values[c] as u128 + v2_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, BITS_NUMBER).0);
    v2_vec_values[b] = ((v1_vec_values[b] ^ v2_vec_values[c]) >> R4)
        ^ (v1_vec_values[b] ^ v2_vec_values[c]) << (64 - R4);
    let (b_result, b_bit, b_3bits) =
        split_value_4bits((v1_vec_values[b] ^ v2_vec_values[c]) as u128, BITS_NUMBER);
    v_xor_b_bit_vec.push(b_result);
    b_bit_vec.push(b_bit);
    b_3bits_vec.push(b_3bits)
}

fn blake2f_circuit<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, InputValues>,
    params: CircuitParams,
) {
    let v_vec: Vec<Queriable<F>> = (0..V_LEN)
        .map(|i| ctx.forward(format!("v_vec[{}]", i).as_str()))
        .collect();
    let h_vec: Vec<Queriable<F>> = (0..H_LEN)
        .map(|i| ctx.forward(format!("input_h[{}]", i).as_str()))
        .collect();
    let m_vec: Vec<Queriable<F>> = (0..M_LEN)
        .map(|i| ctx.forward(format!("m_vec[{}]", i).as_str()))
        .collect();
    let round = ctx.forward("round");

    let blake2f_pre_step = ctx.step_type_def("blake2f_pre_step", |ctx| {
        let v_vec = v_vec.clone();
        let setup_v_vec = v_vec.clone();

        let h_vec = h_vec.clone();
        let setup_h_vec = h_vec.clone();

        let m_vec = m_vec.clone();
        let setup_m_vec = m_vec.clone();

        let t0 = ctx.internal("t0");
        let t1 = ctx.internal("t1");
        let f = ctx.internal("f");

        let h_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("h_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_h_split_4bits_vec = h_split_4bits_vec.clone();

        let m_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..M_LEN)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("m_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_m_split_4bits_vec = m_split_4bits_vec.clone();

        let t_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..2)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("t_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_t_split_4bits_vec = t_split_4bits_vec.clone();

        let iv_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("iv_split_4bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_iv_split_4bits_vec = iv_split_4bits_vec.clone();

        let final_split_bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("final_split_bits_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_final_split_bits_vec = final_split_bits_vec.clone();

        ctx.setup(move |ctx| {
            for (i, &iv) in v_vec[V_LEN / 2..V_LEN].iter().enumerate().take(8) {
                ctx.add_lookup(params.iv_table.apply(i).apply(iv))
            }
            ctx.constr(eq(f * (f - 1), 0));
            for (i, split_4bits_vec) in h_split_4bits_vec.iter().enumerate().take(8) {
                let mut h_4bits_sum_value = 0.expr() * 1;
                for &bits in split_4bits_vec.iter().rev().take(BITS_NUMBER) {
                    ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                    h_4bits_sum_value = h_4bits_sum_value * VALUE_4BITS + bits;
                }
                ctx.constr(eq(h_4bits_sum_value, h_vec[i]))
            }
            for (i, split_4bits_vec) in m_split_4bits_vec.iter().enumerate() {
                let mut m_4bits_sum_value = 0.expr() * 1;
                for &bits in split_4bits_vec.iter().rev().take(BITS_NUMBER) {
                    ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                    m_4bits_sum_value = m_4bits_sum_value * VALUE_4BITS + bits;
                }
                ctx.constr(eq(m_4bits_sum_value, m_vec[i]))
            }
            for (i, split_4bits_vec) in t_split_4bits_vec.iter().enumerate().take(2) {
                let mut t_4bits_sum_value = 0.expr() * 1;
                for &bits in split_4bits_vec.iter().rev().take(BITS_NUMBER) {
                    ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                    t_4bits_sum_value = t_4bits_sum_value * VALUE_4BITS + bits;
                }
                ctx.constr(eq(t_4bits_sum_value, if i == 0 { t0 } else { t1 }));
            }

            for (i, split_4bits_vec) in iv_split_4bits_vec.iter().enumerate().take(3) {
                let mut iv_4bits_sum_value = 0.expr() * 1;
                for &bits in split_4bits_vec.iter().rev().take(BITS_NUMBER) {
                    ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                    iv_4bits_sum_value = iv_4bits_sum_value * VALUE_4BITS + bits;
                }
                ctx.constr(eq(iv_4bits_sum_value, v_vec[i + 12]))
            }

            for i in 0..H_LEN {
                ctx.constr(eq(v_vec[i], h_vec[i]));
            }

            for &v in v_vec.iter().take(12) {
                ctx.transition(eq(v, v.next()));
            }
            ctx.transition(eq(v_vec[15], v_vec[15].next()));

            for &h in h_vec.iter().take(H_LEN) {
                ctx.transition(eq(h, h.next()));
            }
            for &m in m_vec.iter().take(M_LEN) {
                ctx.transition(eq(m, m.next()));
            }

            ctx.constr(eq(round, 0));
            ctx.transition(eq(round, round.next()));

            // v[12] := v[12] ^ (t mod 2**w)
            // v[13] := v[13] ^ (t >> w)
            for (i, (final_plit_bits_value, (iv_split_bits_value, t_split_bits_value))) in
                final_split_bits_vec
                    .iter()
                    .zip(iv_split_4bits_vec.iter().zip(t_split_4bits_vec.iter()))
                    .enumerate()
                    .take(2)
            {
                let mut final_bits_sum_value = 0.expr() * 1;
                for (&value, (&iv, &t)) in final_plit_bits_value
                    .iter()
                    .rev()
                    .zip(
                        iv_split_bits_value
                            .iter()
                            .rev()
                            .zip(t_split_bits_value.iter().rev()),
                    )
                    .take(BITS_NUMBER)
                {
                    ctx.add_lookup(
                        params
                            .xor_4bits_table
                            .apply(iv * VALUE_4BITS + t)
                            .apply(value),
                    );
                    final_bits_sum_value = final_bits_sum_value * VALUE_4BITS + value;
                }
                ctx.constr(eq(final_bits_sum_value, v_vec[12 + i].next()))
            }

            let mut final_bits_sum_value = 0.expr() * 1;
            for (&value, &iv) in final_split_bits_vec[2]
                .iter()
                .rev()
                .zip(iv_split_4bits_vec[2].iter().rev())
            {
                ctx.add_lookup(
                    params
                        .xor_4bits_table
                        .apply(iv * VALUE_4BITS + 0xF)
                        .apply(value),
                );
                final_bits_sum_value = final_bits_sum_value * VALUE_4BITS + value;
            }
            ctx.transition(eq(
                select(f, final_bits_sum_value, v_vec[14]),
                v_vec[14].next(),
            ));
        });

        ctx.wg(move |ctx, inputs: PreInput<F>| {
            ctx.assign(round, inputs.round);
            ctx.assign(t0, inputs.t0);
            ctx.assign(t1, inputs.t1);
            ctx.assign(f, inputs.f);
            for (&q, &v) in setup_v_vec.iter().zip(inputs.v_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_h_vec.iter().zip(inputs.h_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_m_vec.iter().zip(inputs.m_vec.iter()) {
                ctx.assign(q, v)
            }
            for (q_vec, v_vec) in setup_h_split_4bits_vec
                .iter()
                .zip(inputs.h_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_m_split_4bits_vec
                .iter()
                .zip(inputs.m_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_t_split_4bits_vec
                .iter()
                .zip(inputs.t_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_iv_split_4bits_vec
                .iter()
                .zip(inputs.iv_split_4bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_final_split_bits_vec
                .iter()
                .zip(inputs.final_split_bits_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
        })
    });

    let blake2f_g_step_vec: Vec<StepTypeWGHandler<F, _, _>> = (0..MIXING_ROUND)
        .map(|r| {
            ctx.step_type_def("blake2f_g_step", |ctx| {
                let v_vec = v_vec.clone();
                let setup_v_vec = v_vec.clone();
                let h_vec = h_vec.clone();
                let setup_h_vec = h_vec.clone();
                let m_vec = m_vec.clone();
                let setup_m_vec = m_vec.clone();

                let v_mid1_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid1_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid1_vec = v_mid1_vec.clone();
                let v_mid2_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid2_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid2_vec = v_mid2_vec.clone();
                let v_mid3_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid3_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid3_vec = v_mid3_vec.clone();
                let v_mid4_vec: Vec<Queriable<F>> = (0..V_LEN)
                    .map(|i| ctx.internal(format!("v_mid4_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid4_vec = v_mid4_vec.clone();

                let v_mid_va_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
                    .map(|i| {
                        (0..BITS_NUMBER + 1)
                            .map(|j| {
                                ctx.internal(format!("v_mid_va_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_va_bit_vec = v_mid_va_bit_vec.clone();
                let v_mid_vd_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
                    .map(|i| {
                        (0..BITS_NUMBER)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vd_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vd_bit_vec = v_mid_vd_bit_vec.clone();
                let v_mid_vc_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
                    .map(|i| {
                        (0..BITS_NUMBER + 1)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vc_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vc_bit_vec = v_mid_vc_bit_vec.clone();
                let v_mid_vb_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
                    .map(|i| {
                        (0..BITS_NUMBER)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vb_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vb_bit_vec = v_mid_vb_bit_vec.clone();

                let v_xor_d_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUND)
                    .map(|i| {
                        (0..BITS_NUMBER)
                            .map(|j| {
                                ctx.internal(format!("v_xor_d_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_xor_d_bit_vec = v_xor_d_bit_vec.clone();

                let v_xor_b_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUND)
                    .map(|i| {
                        (0..BITS_NUMBER)
                            .map(|j| {
                                ctx.internal(format!("v_xor_b_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_xor_b_bit_vec = v_xor_b_bit_vec.clone();

                let b_bit_vec: Vec<Queriable<F>> = (0..G_ROUND / 2)
                    .map(|i| ctx.internal(format!("b_bit_vec[{}]", i).as_str()))
                    .collect();
                let setup_b_bit_vec = b_bit_vec.clone();
                let b_3bits_vec: Vec<Queriable<F>> = (0..G_ROUND / 2)
                    .map(|i| ctx.internal(format!("b_3bits_vec[{}]", i).as_str()))
                    .collect();
                let setup_b_3bits_vec = b_3bits_vec.clone();

                ctx.setup(move |ctx| {
                    let s = SIGMA_VALUES[r % 10];

                    // Rotation constants | (R1, R2, R3, R4)  | = | (32, 24, 16, 63)
                    for i in 0..G_ROUND {
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

                        let mut a_bits_sum_value = 0.expr() * 1;
                        let mut a_bits_sum_mod_value = 0.expr() * 1;
                        for (j, &bits) in v_mid_va_bit_vec[i].iter().rev().enumerate() {
                            a_bits_sum_value = a_bits_sum_value * VALUE_4BITS + bits;
                            if j != 0 {
                                a_bits_sum_mod_value = a_bits_sum_mod_value * VALUE_4BITS + bits;
                            }
                            ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                        }
                        ctx.constr(eq(
                            a_bits_sum_value,
                            input_vec[a] + input_vec[b] + m_vec[s[i]],
                        ));
                        ctx.constr(eq(a_bits_sum_mod_value, output_vec[a]));

                        let mut d_bits_sum_value = 0.expr() * 1;
                        for &bits in v_mid_vd_bit_vec[i].iter().rev() {
                            d_bits_sum_value = d_bits_sum_value * VALUE_4BITS + bits;
                            ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                        }
                        ctx.constr(eq(d_bits_sum_value, input_vec[d]));

                        let mut ad_xor_sum_value = 0.expr() * 1;
                        for &bits in v_xor_d_bit_vec[i].iter().rev() {
                            ad_xor_sum_value = ad_xor_sum_value * VALUE_4BITS + bits;
                        }
                        ctx.constr(eq(ad_xor_sum_value, output_vec[d]));
                        for j in 0..BITS_NUMBER {
                            ctx.add_lookup(
                                params
                                    .xor_4bits_table
                                    .apply(
                                        v_mid_va_bit_vec[i][j] * VALUE_4BITS
                                            + v_mid_vd_bit_vec[i][j],
                                    )
                                    .apply(
                                        v_xor_d_bit_vec[i][(j + VALUE_4BITS as usize - move1)
                                            % VALUE_4BITS as usize],
                                    ),
                            );
                        }

                        let mut c_bits_sum_value = 0.expr() * 1;
                        let mut c_bits_sum_mod_value = 0.expr() * 1;
                        for (j, &bits) in v_mid_vc_bit_vec[i].iter().rev().enumerate() {
                            c_bits_sum_value = c_bits_sum_value * VALUE_4BITS + bits;
                            if j != 0 {
                                c_bits_sum_mod_value = c_bits_sum_mod_value * VALUE_4BITS + bits;
                            }
                            ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                        }
                        ctx.constr(eq(c_bits_sum_value, input_vec[c] + output_vec[d]));
                        ctx.constr(eq(c_bits_sum_mod_value, output_vec[c]));

                        let mut b_bits_sum_value = 0.expr() * 1;
                        for &bits in v_mid_vb_bit_vec[i].iter().rev() {
                            b_bits_sum_value = b_bits_sum_value * VALUE_4BITS + bits;
                            ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                        }
                        ctx.constr(eq(b_bits_sum_value, input_vec[b]));

                        for j in 0..BITS_NUMBER {
                            ctx.add_lookup(
                                params
                                    .xor_4bits_table
                                    .apply(
                                        v_mid_vb_bit_vec[i][j] * VALUE_4BITS
                                            + v_mid_vc_bit_vec[i][j],
                                    )
                                    .apply(
                                        v_xor_b_bit_vec[i][(j + VALUE_4BITS as usize - move2)
                                            % VALUE_4BITS as usize],
                                    ),
                            );
                        }

                        let mut bc_xor_sum_value = 0.expr() * 1;
                        for (j, &bits) in v_xor_b_bit_vec[i].iter().rev().enumerate() {
                            if j == 0 && i % 2 == 1 {
                                bc_xor_sum_value = b_3bits_vec[i / 2] * 1;
                                ctx.constr(eq(b_bit_vec[i / 2] * 8 + b_3bits_vec[i / 2], bits));
                            } else {
                                bc_xor_sum_value = bc_xor_sum_value * VALUE_4BITS + bits;
                            }
                            ctx.add_lookup(params.bits_table.apply(bits).apply(bits));
                        }
                        if i % 2 == 1 {
                            bc_xor_sum_value = bc_xor_sum_value * 2 + b_bit_vec[i / 2];

                            ctx.constr(eq(b_bit_vec[i / 2] * (b_bit_vec[i / 2] - 1), 0));
                            // To constraint b_3bits_vec[i/2] \in [0..8)
                            ctx.add_lookup(
                                params
                                    .bits_table
                                    .apply(b_3bits_vec[i / 2])
                                    .apply(b_3bits_vec[i / 2]),
                            );
                            ctx.add_lookup(
                                params
                                    .bits_table
                                    .apply(b_3bits_vec[i / 2] * 2)
                                    .apply(b_3bits_vec[i / 2] * 2),
                            );
                        }
                        ctx.constr(eq(bc_xor_sum_value, output_vec[b]));
                    }
                    for (&v, &new_v) in v_vec.iter().zip(v_mid4_vec.iter()) {
                        ctx.transition(eq(new_v, v.next()));
                    }

                    for &h in h_vec.iter() {
                        ctx.transition(eq(h, h.next()));
                    }
                    if r < MIXING_ROUND - 1 {
                        for &m in m_vec.iter() {
                            ctx.transition(eq(m, m.next()));
                        }
                    }
                    ctx.constr(eq(round, r));
                    ctx.transition(eq(round + 1, round.next()));
                });

                ctx.wg(move |ctx, inputs: GInput<F>| {
                    ctx.assign(round, inputs.round);
                    for (&q, &v) in setup_v_vec.iter().zip(inputs.v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_h_vec.iter().zip(inputs.h_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_m_vec.iter().zip(inputs.m_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_v_mid1_vec.iter().zip(inputs.v_mid1_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_v_mid2_vec.iter().zip(inputs.v_mid2_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_v_mid3_vec.iter().zip(inputs.v_mid3_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_v_mid4_vec.iter().zip(inputs.v_mid4_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (q_vec, v_vec) in setup_v_mid_va_bit_vec
                        .iter()
                        .zip(inputs.v_mid_va_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in setup_v_mid_vb_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vb_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in setup_v_mid_vc_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vc_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in setup_v_mid_vd_bit_vec
                        .iter()
                        .zip(inputs.v_mid_vd_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in setup_v_xor_d_bit_vec
                        .iter()
                        .zip(inputs.v_xor_d_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (q_vec, v_vec) in setup_v_xor_b_bit_vec
                        .iter()
                        .zip(inputs.v_xor_b_bit_vec.iter())
                    {
                        for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    }
                    for (&q, &v) in setup_b_bit_vec.iter().zip(inputs.b_bit_vec.iter()) {
                        ctx.assign(q, v)
                    }
                    for (&q, &v) in setup_b_3bits_vec.iter().zip(inputs.b_3bits_vec.iter()) {
                        ctx.assign(q, v)
                    }
                })
            })
        })
        .collect();

    let blake2f_final_step = ctx.step_type_def("blake2f_final_step", |ctx| {
        let v_vec = v_vec.clone();
        let setup_v_vec = v_vec.clone();

        let h_vec = h_vec.clone();
        let setup_h_vec = h_vec.clone();

        let output_vec = m_vec.clone();
        let setup_output_vec = output_vec.clone();

        let v_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("v_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_v_split_bit_vec = v_split_bit_vec.clone();

        let h_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("h_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_h_split_bit_vec = h_split_bit_vec.clone();

        let v_xor_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_v_xor_split_bit_vec = v_xor_split_bit_vec.clone();

        let final_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
            .map(|i| {
                (0..BITS_NUMBER)
                    .map(|j| ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_final_split_bit_vec = final_split_bit_vec.clone();

        ctx.setup(move |ctx| {
            for (&v, v_split) in v_vec.iter().zip(v_split_bit_vec.iter()) {
                let mut v_4bits_sum_value = 0.expr() * 1;
                for &value in v_split.iter().rev() {
                    v_4bits_sum_value = v_4bits_sum_value * VALUE_4BITS + value;
                }
                ctx.constr(eq(v_4bits_sum_value, v));
            }
            for (&h, h_split) in h_vec.iter().zip(h_split_bit_vec.iter()) {
                let mut h_4bits_sum_value = 0.expr() * 1;
                for &value in h_split.iter().rev() {
                    h_4bits_sum_value = h_4bits_sum_value * VALUE_4BITS + value;
                }
                ctx.constr(eq(h_4bits_sum_value, h));
            }

            for (xor_vec, (v1_vec, v2_vec)) in v_xor_split_bit_vec.iter().zip(
                v_split_bit_vec[0..V_LEN / 2]
                    .iter()
                    .zip(v_split_bit_vec[V_LEN / 2..V_LEN].iter()),
            ) {
                for (&xor, (&v1, &v2)) in xor_vec.iter().zip(v1_vec.iter().zip(v2_vec.iter())) {
                    ctx.add_lookup(
                        params
                            .xor_4bits_table
                            .apply(v1 * VALUE_4BITS + v2)
                            .apply(xor),
                    );
                }
            }

            for (final_vec, (xor_vec, h_vec)) in final_split_bit_vec
                .iter()
                .zip(v_xor_split_bit_vec.iter().zip(h_split_bit_vec.iter()))
            {
                for (&value, (&v1, &v2)) in final_vec.iter().zip(xor_vec.iter().zip(h_vec.iter())) {
                    ctx.add_lookup(
                        params
                            .xor_4bits_table
                            .apply(v1 * VALUE_4BITS + v2)
                            .apply(value),
                    );
                }
            }

            for (final_vec, &output) in final_split_bit_vec.iter().zip(output_vec.iter()) {
                let mut final_4bits_sum_value = 0.expr() * 1;
                for &value in final_vec.iter().rev() {
                    final_4bits_sum_value = final_4bits_sum_value * VALUE_4BITS + value;
                }
                ctx.constr(eq(output, final_4bits_sum_value));
            }
            ctx.constr(eq(round, MIXING_ROUND));
        });

        ctx.wg(move |ctx, inputs: FinalInput<F>| {
            ctx.assign(round, inputs.round);
            for (&q, &v) in setup_v_vec.iter().zip(inputs.v_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_h_vec.iter().zip(inputs.h_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_output_vec.iter().zip(inputs.output_vec.iter()) {
                ctx.assign(q, v)
            }

            for (q_vec, v_vec) in setup_v_split_bit_vec
                .iter()
                .zip(inputs.v_split_bit_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_h_split_bit_vec
                .iter()
                .zip(inputs.h_split_bit_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_v_xor_split_bit_vec
                .iter()
                .zip(inputs.v_xor_split_bit_vec.iter())
            {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
            for (q_vec, v_vec) in setup_final_split_bit_vec
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

    ctx.pragma_num_steps(MIXING_ROUND + 2);

    ctx.trace(move |ctx, values| {
        // println!("h_vec = {:x?}", values.h_vec.to_vec());
        // println!("m_vec = {:x?}", values.m_vec.to_vec());
        // println!("t0 = {:x?}, t1 = {:x?}", values.t0, values.t1);

        let h_vec_values = values.h_vec.to_vec();
        let h_split_4bits_vec = h_vec_values
            .iter()
            .map(|&value| {
                let mut value = value;
                (0..BITS_NUMBER)
                    .map(|_| {
                        let v = value % VALUE_4BITS;
                        value >>= 4;
                        F::from(v)
                    })
                    .collect()
            })
            .collect();

        let m_vec_values = values.m_vec.to_vec();
        let m_split_4bits_vec = m_vec_values
            .iter()
            .map(|&value| {
                let mut value = value;
                (0..BITS_NUMBER)
                    .map(|_| {
                        let v = value % VALUE_4BITS;
                        value >>= 4;
                        F::from(v)
                    })
                    .collect()
            })
            .collect();

        let mut iv_vec_values = IV_VALUES.to_vec();
        let iv_split_4bits_vec: Vec<Vec<F>> = iv_vec_values[4..7]
            .iter()
            .map(|&value| {
                let mut value = value;
                (0..BITS_NUMBER)
                    .map(|_| {
                        let v = value % VALUE_4BITS;
                        value >>= 4;
                        F::from(v)
                    })
                    .collect()
            })
            .collect();

        let mut v_vec_values = h_vec_values.clone();
        v_vec_values.append(&mut iv_vec_values);

        let mut value = values.t0;
        let t0_split_4bits_vec = (0..BITS_NUMBER)
            .map(|_| {
                let v = value % VALUE_4BITS;
                value >>= 4;
                F::from(v)
            })
            .collect();
        let mut value = values.t1;
        let t1_split_4bits_vec = (0..BITS_NUMBER)
            .map(|_| {
                let v = value % VALUE_4BITS;
                value >>= 4;
                F::from(v)
            })
            .collect();

        let final_values = vec![
            v_vec_values[12] ^ values.t0,
            v_vec_values[13] ^ values.t1,
            v_vec_values[14] ^ 0xFFFFFFFFFFFFFFFF,
        ];
        let final_split_bits_vec: Vec<Vec<F>> = final_values
            .iter()
            .map(|&value| {
                let mut value = value;
                (0..BITS_NUMBER)
                    .map(|_| {
                        let v = value % VALUE_4BITS;
                        value >>= 4;
                        F::from(v)
                    })
                    .collect()
            })
            .collect();

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
            t_split_4bits_vec: vec![t0_split_4bits_vec, t1_split_4bits_vec],
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

            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (0, 4, 8, 12),
                (m_vec_values[s[0]], m_vec_values[s[1]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (1, 5, 9, 13),
                (m_vec_values[s[2]], m_vec_values[s[3]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (2, 6, 10, 14),
                (m_vec_values[s[4]], m_vec_values[s[5]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
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
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (0, 5, 10, 15),
                (m_vec_values[s[8]], m_vec_values[s[9]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (1, 6, 11, 12),
                (m_vec_values[s[10]], m_vec_values[s[11]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (2, 7, 8, 13),
                (m_vec_values[s[12]], m_vec_values[s[13]]),
                (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
                (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
                (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
                (&mut b_bit_vec, &mut b_3bits_vec),
            );
            g_internal(
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
            ctx.add(&blake2f_g_step_vec[r as usize], ginputs);
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
                .map(|&v| split_value_4bits(v as u128, BITS_NUMBER).0)
                .collect(),
            h_split_bit_vec: h_vec_values
                .iter()
                .map(|&v| split_value_4bits(v as u128, BITS_NUMBER).0)
                .collect(),
            v_xor_split_bit_vec: v_vec_values[0..V_LEN / 2]
                .iter()
                .zip(v_vec_values[V_LEN / 2..V_LEN].iter())
                .map(|(&v1, &v2)| split_xor_value(v1, v2))
                .collect(),
            final_split_bit_vec: output_vec_values
                .iter()
                .map(|&output| split_value_4bits(output as u128, BITS_NUMBER).0)
                .collect(),
        };
        ctx.add(&blake2f_final_step, final_inputs);
        // ba80a53f981c4d0d, 6a2797b69f12f6e9, 4c212f14685ac4b7, 4b12bb6fdbffa2d1
        // 7d87c5392aab792d, c252d5de4533cc95, 18d38aa8dbf1925a,b92386edd4009923
        println!("output = {:x?}", output_vec_values);
    })
}

fn blake2f_super_circuit<F: PrimeField + Hash>() -> SuperCircuit<F, InputValues> {
    super_circuit::<F, InputValues, _>("blake2f", |ctx| {
        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        let (_, iv_table) = ctx.sub_circuit(single_config.clone(), blake2f_iv_table, IV_LENGTH);
        let (_, bits_table) =
            ctx.sub_circuit(single_config.clone(), blake2f_4bits_table, BITS_NUMBER);
        let (_, xor_4bits_table) = ctx.sub_circuit(
            single_config,
            blake2f_xor_4bits_table,
            BITS_NUMBER * BITS_NUMBER,
        );
        // let (_, extend_4bits_table) = ctx.sub_circuit(single_config, blake2f_extend_4bits_table,
        // BITS_NUMBER);

        let maxwidth_config = config(
            MaxWidthCellManager::new(2, true),
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

    let values = InputValues {
        round: 12,
        // h[0] = hex"48c9bdf267e6096a 3ba7ca8485ae67bb 2bf894fe72f36e3c f1361d5f3af54fa5";
        // h[1] = hex"d182e6ad7f520e51 1f6c3e2b8c68059b 6bbd41fbabd9831f 79217e1319cde05b";
        h_vec: [
            0x6a09e667f2bdc948,
            0xbb67ae8584caa73b,
            0x3c6ef372fe94f82b,
            0xa54ff53a5f1d36f1,
            0x510e527fade682d1,
            0x9b05688c2b3e6c1f,
            0x1f83d9abfb41bd6b,
            0x5be0cd19137e2179,
        ], // 8 * 64bits
        // m[0] = hex"6162630000000000000000000000000000000000000000000000000000000000";
        // m[1] = hex"0000000000000000000000000000000000000000000000000000000000000000";
        // m[2] = hex"0000000000000000000000000000000000000000000000000000000000000000";
        // m[3] = hex"0000000000000000000000000000000000000000000000000000000000000000";
        m_vec: [0x636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // 16 * 64bits
        t0: 3,                                                          // 64bits
        t1: 0,                                                          // 64bits
        f: true,                                                        // 8bits
    };
    let circuit =
        ChiquitoHalo2SuperCircuit::new(compiled, super_circuit.get_mapping().generate(values));

    let prover = MockProver::run(14, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}
