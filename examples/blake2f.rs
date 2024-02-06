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
pub const SIGMA_VECTOR_NUMBER: usize = 12;
pub const SIGMA_VECTOR_LENGTH: usize = 16;
pub const SIGMA_LENGTH: usize = SIGMA_VECTOR_NUMBER * SIGMA_VECTOR_LENGTH;
pub const CONSTANT_LENGTH: usize = 4;
pub const XOR_LENGTH: usize = 64;
pub const SPLIT_LENGTH: usize = 16;
pub const R1: usize = 32;
pub const R2: usize = 24;
pub const R3: usize = 16;
pub const R4: usize = 63;

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
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
];

fn split_value<F: PrimeField + Hash>(len: usize, value: u128) -> Vec<F> {
    let mut value = value;
    (0..len)
        .map(|_| {
            let b = (value % 2) as u64;
            value /= 2;
            F::from(b)
        })
        .collect()
}

// Rotation constants | (R1, R2, R3, R4)  | = | (32, 24, 16, 63)

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

struct CircuitParams {
    pub iv_table: LookupTable,
}

struct PreInput<F> {
    round: F,
    t0: F,
    t1: F,
    f: F,
    v_vec: Vec<F>,
    h_vec: Vec<F>,
    m_vec: Vec<F>,
    iv_vec: Vec<F>,
    split_bit_vec: Vec<Vec<F>>,
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
}

struct FinalInput<F> {
    round: F,
    v_vec: Vec<F>,
    h_vec: Vec<F>,
    m_vec: Vec<F>,
    output_vec: Vec<F>,
    v_split_bit_vec: Vec<Vec<F>>,
    h_split_bit_vec: Vec<Vec<F>>,
}

#[derive(Default)]
struct InputValues {
    pub round: u32,       // 32bit
    pub h_vec: [u64; 8],  // 8 * 64bits
    pub m_vec: [u64; 16], // 16 * 64bits
    pub t0: u64,          // 64bits
    pub t1: u64,          // 64bits
    pub f: bool,          // 8bits
}

fn g_internal<F: PrimeField + Hash>(
    (v1_vec_values, v2_vec_values): (&mut [u64], &mut [u64]),
    (a, b, c, d): (usize, usize, usize, usize),
    (x, y): (u64, u64),
    va_bit_vec: &mut Vec<Vec<F>>,
    vb_bit_vec: &mut Vec<Vec<F>>,
    vc_bit_vec: &mut Vec<Vec<F>>,
    vd_bit_vec: &mut Vec<Vec<F>>,
) {
    va_bit_vec.push(split_value(
        66,
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128,
    ));
    vd_bit_vec.push(split_value(64, v1_vec_values[d] as u128));
    v1_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128) as u64;
    v1_vec_values[d] = ((v1_vec_values[d] ^ v1_vec_values[a]) >> R1)
        ^ (v1_vec_values[d] ^ v1_vec_values[a]) << (64 - R1);

    vc_bit_vec.push(split_value(
        65,
        v1_vec_values[c] as u128 + v1_vec_values[d] as u128,
    ));
    vb_bit_vec.push(split_value(64, v1_vec_values[b] as u128));
    v1_vec_values[c] = (v1_vec_values[c] as u128 + v1_vec_values[d] as u128) as u64;
    v1_vec_values[b] = ((v1_vec_values[b] ^ v1_vec_values[c]) >> R2)
        ^ (v1_vec_values[b] ^ v1_vec_values[c]) << (64 - R2);

    va_bit_vec.push(split_value(
        66,
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128,
    ));
    vd_bit_vec.push(split_value(64, v1_vec_values[d] as u128));
    v2_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128) as u64;
    v2_vec_values[d] = ((v1_vec_values[d] ^ v2_vec_values[a]) >> R3)
        ^ (v1_vec_values[d] ^ v2_vec_values[a]) << (64 - R3);
    vc_bit_vec.push(split_value(
        65,
        v1_vec_values[c] as u128 + v2_vec_values[d] as u128,
    ));
    vb_bit_vec.push(split_value(64, v1_vec_values[b] as u128));
    v2_vec_values[c] = (v1_vec_values[c] as u128 + v2_vec_values[d] as u128) as u64;
    v2_vec_values[b] = ((v1_vec_values[b] ^ v2_vec_values[c]) >> R4)
        ^ (v1_vec_values[b] ^ v2_vec_values[c]) << (64 - R4);
}

fn blake2f_circuit<F: PrimeField + Hash>(
    ctx: &mut CircuitContext<F, InputValues>,
    params: CircuitParams,
) {
    let v_vec: Vec<Queriable<F>> = (0..16)
        .map(|i| ctx.forward(format!("v_vec[{}]", i).as_str()))
        .collect();
    let h_vec: Vec<Queriable<F>> = (0..8)
        .map(|i| ctx.forward(format!("input_h[{}]", i).as_str()))
        .collect();
    let m_vec: Vec<Queriable<F>> = (0..16)
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

        let iv_vec: Vec<Queriable<F>> = (0..8)
            .map(|i| ctx.internal(format!("iv_vec[{}]", i).as_str()))
            .collect();
        let setup_iv_vec = iv_vec.clone();

        let split_bit_vec: Vec<Vec<Queriable<F>>> = (0..5)
            .map(|i| {
                (0..64)
                    .map(|j| ctx.internal(format!("split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_split_bit_vec = split_bit_vec.clone();

        let t0 = ctx.internal("t0");
        let t1 = ctx.internal("t1");
        let f = ctx.internal("f");

        ctx.setup(move |ctx| {
            for (i, &iv) in iv_vec.iter().enumerate().take(8) {
                ctx.add_lookup(params.iv_table.apply(i).apply(iv))
            }
            for i in 0..8 {
                ctx.constr(eq(v_vec[i], h_vec[i]));
                ctx.constr(eq(v_vec[i + 8], iv_vec[i]));
            }
            ctx.constr(eq(f * (f - 1), 0));

            for split_bit_vec in split_bit_vec.iter().take(5) {
                for &split_bit in split_bit_vec.iter().take(5) {
                    ctx.constr(eq(split_bit * (split_bit - 1), 0))
                }
            }

            // v[12] = v[12] ^ t0
            // todo: change to lookup table
            let mut v12_sum_split_value = split_bit_vec[0][63] * 1;
            let mut t0_sum_split_value = split_bit_vec[1][63] * 1;
            let mut xor_v12_t0_sum_split_value = split_bit_vec[0][63] + split_bit_vec[1][63]
                - split_bit_vec[0][63] * split_bit_vec[1][63] * 2;
            for j in 0..63 {
                v12_sum_split_value = v12_sum_split_value * 2 + split_bit_vec[0][63 - j - 1];
                t0_sum_split_value = t0_sum_split_value * 2 + split_bit_vec[1][63 - j - 1];
                xor_v12_t0_sum_split_value = xor_v12_t0_sum_split_value * 2
                    + (split_bit_vec[0][63 - j - 1] + split_bit_vec[1][63 - j - 1]
                        - split_bit_vec[0][63 - j - 1] * split_bit_vec[1][63 - j - 1] * 2);
            }
            ctx.constr(eq(v12_sum_split_value, v_vec[12]));
            ctx.constr(eq(t0_sum_split_value, t0));

            // v[13] = v[13] ^ t1
            let mut v13_sum_split_value = split_bit_vec[2][63] * 1;
            let mut t1_sum_split_value = split_bit_vec[3][63] * 1;
            let mut xor_v13_t1_sum_split_value = split_bit_vec[2][63] + split_bit_vec[3][63]
                - split_bit_vec[2][63]
                    * split_bit_vec[3][63]
                    * (split_bit_vec[2][63] + split_bit_vec[3][63]);
            for j in 0..63 {
                v13_sum_split_value = v13_sum_split_value * 2 + split_bit_vec[2][63 - j - 1];
                t1_sum_split_value = t1_sum_split_value * 2 + split_bit_vec[3][63 - j - 1];
                xor_v13_t1_sum_split_value = xor_v13_t1_sum_split_value * 2
                    + (split_bit_vec[2][63 - j - 1] + split_bit_vec[3][63 - j - 1]
                        - split_bit_vec[2][63 - j - 1] * split_bit_vec[3][63 - j - 1] * 2);
            }
            ctx.constr(eq(v13_sum_split_value, v_vec[13]));
            ctx.constr(eq(t1_sum_split_value, t1));

            // if f {
            //  v[14] = v[14] ^ 0xFF..FF
            //}
            let mut v14_sum_split_value = split_bit_vec[4][63] * 1;
            let mut xor_v14_sum_split_value = 1u64.expr() - split_bit_vec[4][63];
            for j in 0..63 {
                v14_sum_split_value = v14_sum_split_value * 2 + split_bit_vec[4][63 - j - 1];
                xor_v14_sum_split_value =
                    xor_v14_sum_split_value * 2 + (1u64.expr() - split_bit_vec[4][63 - j - 1])
            }

            ctx.transition(eq(xor_v12_t0_sum_split_value, v_vec[12].next()));
            ctx.transition(eq(xor_v13_t1_sum_split_value, v_vec[13].next()));
            ctx.transition(eq(
                select(f, xor_v14_sum_split_value, v_vec[14]),
                v_vec[14].next(),
            ));
            for &v in v_vec.iter().take(12) {
                ctx.transition(eq(v, v.next()));
            }
            ctx.transition(eq(v_vec[15], v_vec[15].next()));

            for &h in h_vec.iter().take(8) {
                ctx.transition(eq(h, h.next()));
            }
            for &m in m_vec.iter().take(16) {
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
            for (&q, &v) in setup_v_vec.iter().zip(inputs.v_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_h_vec.iter().zip(inputs.h_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_m_vec.iter().zip(inputs.m_vec.iter()) {
                ctx.assign(q, v)
            }
            for (&q, &v) in setup_iv_vec.iter().zip(inputs.iv_vec.iter()) {
                ctx.assign(q, v)
            }
            for (q_vec, v_vec) in setup_split_bit_vec.iter().zip(inputs.split_bit_vec.iter()) {
                for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(q, v)
                }
            }
        })
    });

    let blake2f_g_step_vec: Vec<StepTypeWGHandler<F, _, _>> = (0..12)
        .map(|r| {
            ctx.step_type_def("blake2f_g_step", |ctx| {
                let v_vec = v_vec.clone();
                let setup_v_vec = v_vec.clone();
                let h_vec = h_vec.clone();
                let setup_h_vec = h_vec.clone();
                let m_vec = m_vec.clone();
                let setup_m_vec = m_vec.clone();

                let v_mid1_vec: Vec<Queriable<F>> = (0..16)
                    .map(|i| ctx.internal(format!("v_mid1_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid1_vec = v_mid1_vec.clone();
                let v_mid2_vec: Vec<Queriable<F>> = (0..16)
                    .map(|i| ctx.internal(format!("v_mid2_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid2_vec = v_mid2_vec.clone();
                let v_mid3_vec: Vec<Queriable<F>> = (0..16)
                    .map(|i| ctx.internal(format!("v_mid3_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid3_vec = v_mid3_vec.clone();
                let v_mid4_vec: Vec<Queriable<F>> = (0..16)
                    .map(|i| ctx.internal(format!("v_mid4_vec[{}]", i).as_str()))
                    .collect();
                let setup_v_mid4_vec = v_mid4_vec.clone();

                let v_mid_va_bit_vec: Vec<Vec<Queriable<F>>> = (0..16)
                    .map(|i| {
                        (0..66)
                            .map(|j| {
                                ctx.internal(format!("v_mid_va_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_va_bit_vec = v_mid_va_bit_vec.clone();
                let v_mid_vd_bit_vec: Vec<Vec<Queriable<F>>> = (0..16)
                    .map(|i| {
                        (0..64)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vd_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vd_bit_vec = v_mid_vd_bit_vec.clone();
                let v_mid_vc_bit_vec: Vec<Vec<Queriable<F>>> = (0..16)
                    .map(|i| {
                        (0..65)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vc_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vc_bit_vec = v_mid_vc_bit_vec.clone();
                let v_mid_vb_bit_vec: Vec<Vec<Queriable<F>>> = (0..16)
                    .map(|i| {
                        (0..64)
                            .map(|j| {
                                ctx.internal(format!("v_mid_vb_bit_vec[{}][{}]", i, j).as_str())
                            })
                            .collect()
                    })
                    .collect();
                let setup_v_mid_vb_bit_vec = v_mid_vb_bit_vec.clone();

                ctx.setup(move |ctx| {
                    let s = SIGMA_VALUES[r % 10];

                    // fn G(a: usize, b: usize, c: usize, d: usize, x: u64, y: u64){
                    //     a' = a + b + x mod 2^64
                    //     d' = d xor a' >>> R1
                    //     c' = c + d' mod 2^64
                    //     b' = b xor c' >>> R2

                    //     a'' = a' + b' + y mod 2^64, a'' = a + b + x + y + (b xor c + (d xor (a +
                    // b + x)) >>> R1) >>> R2 mod 2^64     d'' = d' xor a'' >>>
                    // R3,     c'' = c' + d'' mod 2^64
                    //     b'' = b' xor c'' >>> R4
                    // }
                    for i in 0..16 {
                        for j in 0..66 {
                            ctx.constr(eq(
                                v_mid_va_bit_vec[i][j] * (v_mid_va_bit_vec[i][j] - 1),
                                0,
                            ));
                        }
                        for j in 0..64 {
                            ctx.constr(eq(
                                v_mid_vd_bit_vec[i][j] * (v_mid_vd_bit_vec[i][j] - 1),
                                0,
                            ));
                        }
                        for j in 0..65 {
                            ctx.constr(eq(
                                v_mid_vc_bit_vec[i][j] * (v_mid_vc_bit_vec[i][j] - 1),
                                0,
                            ));
                        }
                        for j in 0..64 {
                            ctx.constr(eq(
                                v_mid_vb_bit_vec[i][j] * (v_mid_vb_bit_vec[i][j] - 1),
                                0,
                            ));
                        }
                    }

                    // Rotation constants | (R1, R2, R3, R4)  | = | (32, 24, 16, 63)
                    for i in 0..16 {
                        let mut pre_vec = v_vec.clone();
                        let mut final_vec = v_mid1_vec.clone();
                        if i < 8 && i % 2 == 1 {
                            pre_vec = v_mid1_vec.clone();
                            final_vec = v_mid2_vec.clone();
                        } else if i >= 8 && i % 2 == 0 {
                            pre_vec = v_mid2_vec.clone();
                            final_vec = v_mid3_vec.clone();
                        } else if i >= 8 && i % 2 == 1 {
                            pre_vec = v_mid3_vec.clone();
                            final_vec = v_mid4_vec.clone();
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

                        let mut move1 = R1;
                        let mut move2 = R2;
                        if i % 2 == 1 {
                            move1 = R3;
                            move2 = R4;
                        }

                        // v[a] = (v[a] + v[b] + x) mod 2^64
                        let mut a_sum_split_value = v_mid_va_bit_vec[i][65] * 1;
                        for j in 0..65 {
                            a_sum_split_value =
                                a_sum_split_value * 2 + v_mid_va_bit_vec[i][65 - j - 1];
                        }
                        ctx.constr(eq(a_sum_split_value, pre_vec[a] + pre_vec[b] + m_vec[s[i]]));

                        let mut a_sum_split_value_mod = v_mid_va_bit_vec[i][63] * 1;
                        for j in 0..63 {
                            a_sum_split_value_mod =
                                a_sum_split_value_mod * 2 + v_mid_va_bit_vec[i][63 - j - 1];
                        }
                        ctx.constr(eq(a_sum_split_value_mod, final_vec[a]));

                        // v[d] = (v[d] ^ v[a]) >>> 32
                        let mut d_sum_split_value = v_mid_vd_bit_vec[i][63] * 1;
                        let mut a_d_xor_sum_split_value = v_mid_vd_bit_vec[i][(63 + move1) % 64]
                            + v_mid_va_bit_vec[i][(63 + move1) % 64]
                            - v_mid_vd_bit_vec[i][(63 + move1) % 64]
                                * v_mid_va_bit_vec[i][(63 + move1) % 64]
                                * 2;
                        for j in 0..63 {
                            d_sum_split_value =
                                d_sum_split_value * 2 + v_mid_vd_bit_vec[i][(63 - j - 1) % 64];
                            a_d_xor_sum_split_value = a_d_xor_sum_split_value * 2
                                + (v_mid_vd_bit_vec[i][(63 + move1 - j - 1) % 64]
                                    + v_mid_va_bit_vec[i][(63 + move1 - j - 1) % 64]
                                    - v_mid_vd_bit_vec[i][(63 + move1 - j - 1) % 64]
                                        * v_mid_va_bit_vec[i][(63 + move1 - j - 1) % 64]
                                        * 2);
                        }
                        ctx.constr(eq(d_sum_split_value, pre_vec[d]));
                        ctx.constr(eq(a_d_xor_sum_split_value, final_vec[d]));

                        // v[c] = (v[c] + v[d]) mod 2^64
                        let mut cd_sum_split_value = v_mid_vc_bit_vec[i][64] * 1;
                        for j in 0..64 {
                            cd_sum_split_value =
                                cd_sum_split_value * 2 + v_mid_vc_bit_vec[i][64 - j - 1];
                        }
                        ctx.constr(eq(cd_sum_split_value, pre_vec[c] + final_vec[d]));
                        let mut cd_sum_split_value_mod = v_mid_vc_bit_vec[i][63] * 1;
                        for j in 0..63 {
                            cd_sum_split_value_mod =
                                cd_sum_split_value_mod * 2 + v_mid_vc_bit_vec[i][63 - j - 1];
                        }
                        ctx.constr(eq(cd_sum_split_value_mod, final_vec[c]));

                        // v[b] = (v[b] ^ v[c]) >>> 24
                        let mut b_sum_split_value = v_mid_vb_bit_vec[i][63] * 1;
                        for j in 0..63 {
                            b_sum_split_value =
                                b_sum_split_value * 2 + v_mid_vb_bit_vec[i][63 - j - 1];
                        }
                        ctx.constr(eq(b_sum_split_value, pre_vec[b]));
                        let mut cb_xor_sum_split_value = v_mid_vb_bit_vec[i][(63 + move2) % 64]
                            + v_mid_vc_bit_vec[i][(63 + move2) % 64]
                            - v_mid_vb_bit_vec[i][(63 + move2) % 64]
                                * v_mid_vc_bit_vec[i][(63 + move2) % 64]
                                * 2;
                        for j in 0..63 {
                            cb_xor_sum_split_value = cb_xor_sum_split_value * 2
                                + (v_mid_vb_bit_vec[i][(63 + move2 - j - 1) % 64]
                                    + v_mid_vc_bit_vec[i][(63 + move2 - j - 1) % 64]
                                    - v_mid_vb_bit_vec[i][(63 + move2 - j - 1) % 64]
                                        * v_mid_vc_bit_vec[i][(63 + move2 - j - 1) % 64]
                                        * 2);
                        }
                        ctx.constr(eq(cb_xor_sum_split_value, final_vec[b]));
                    }

                    for &h in h_vec.iter().take(8) {
                        ctx.transition(eq(h, h.next()));
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
                })
            })
        })
        .collect();

    let blake2f_final_step = ctx.step_type_def("blake2f_final_step", |ctx| {
        let v_vec = v_vec.clone();
        let setup_v_vec = v_vec.clone();

        let h_vec = h_vec.clone();
        let setup_h_vec = h_vec.clone();

        let m_vec = m_vec.clone();
        let setup_m_vec = m_vec.clone();

        let output_vec: Vec<Queriable<F>> = (0..8)
            .map(|i| ctx.internal(format!("output_vec[{}]", i).as_str()))
            .collect();
        let setup_output_vec = output_vec.clone();

        let v_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..16)
            .map(|i| {
                (0..64)
                    .map(|j| ctx.internal(format!("v_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_v_split_bit_vec = v_split_bit_vec.clone();
        let h_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
            .map(|i| {
                (0..64)
                    .map(|j| ctx.internal(format!("h_split_bit_vec[{}][{}]", i, j).as_str()))
                    .collect()
            })
            .collect();
        let setup_h_split_bit_vec = h_split_bit_vec.clone();

        ctx.setup(move |ctx| {
            // todo lookup table
            for i in 0..7 {
                for j in 0..64 {
                    ctx.constr(eq(v_split_bit_vec[i][j] * (v_split_bit_vec[i][j] - 1), 0));
                    ctx.constr(eq(
                        v_split_bit_vec[i + 8][j] * (v_split_bit_vec[i + 8][j] - 1),
                        0,
                    ));
                    ctx.constr(eq(h_split_bit_vec[i][j] * (h_split_bit_vec[i][j] - 1), 0));
                }

                let mut v_pre_sum_split_value = v_split_bit_vec[i][63] * 1;
                let mut v_final_sum_split_value = v_split_bit_vec[i + 8][63] * 1;
                let mut h_sum_split_value = h_split_bit_vec[i][63] * 1;
                let mut xor_sum_split_value =
                    h_split_bit_vec[i][63] + v_split_bit_vec[i][63] + v_split_bit_vec[i + 8][63]
                        - (v_split_bit_vec[i][63] * v_split_bit_vec[i + 8][63]
                            + h_split_bit_vec[i][63] * v_split_bit_vec[i][63]
                            + h_split_bit_vec[i][63] * v_split_bit_vec[i + 8][63])
                            * 2
                        + h_split_bit_vec[i][63]
                            * v_split_bit_vec[i][63]
                            * v_split_bit_vec[i + 8][63]
                            * 4;
                for j in 0..63 {
                    v_pre_sum_split_value =
                        v_pre_sum_split_value * 2 + v_split_bit_vec[i][63 - j - 1];
                    v_final_sum_split_value =
                        v_final_sum_split_value * 2 + v_split_bit_vec[i + 8][63 - j - 1];
                    h_sum_split_value = h_sum_split_value * 2 + h_split_bit_vec[i][63 - j - 1];
                    xor_sum_split_value = xor_sum_split_value * 2
                        + (h_split_bit_vec[i][63 - j - 1]
                            + v_split_bit_vec[i][63 - j - 1]
                            + v_split_bit_vec[i + 8][63 - j - 1]
                            - (v_split_bit_vec[i][63 - j - 1] * v_split_bit_vec[i + 8][63 - j - 1]
                                + h_split_bit_vec[i][63 - j - 1] * v_split_bit_vec[i][63 - j - 1]
                                + h_split_bit_vec[i][63 - j - 1]
                                    * v_split_bit_vec[i + 8][63 - j - 1])
                                * 2
                            + h_split_bit_vec[i][63 - j - 1]
                                * v_split_bit_vec[i][63 - j - 1]
                                * v_split_bit_vec[i + 8][63 - j - 1]
                                * 4)
                }

                ctx.constr(eq(v_pre_sum_split_value, v_vec[i]));
                ctx.constr(eq(v_final_sum_split_value, v_vec[i + 8]));
                ctx.constr(eq(h_sum_split_value, h_vec[i]));
                ctx.constr(eq(xor_sum_split_value, output_vec[i]));
            }
            for &h in h_vec.iter() {
                ctx.transition(eq(h, h.next()));
            }
            for &m in m_vec.iter() {
                ctx.transition(eq(m, m.next()));
            }
            ctx.constr(eq(round, 12));
        });

        ctx.wg(move |ctx, inputs: FinalInput<F>| {
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
        })
    });

    ctx.pragma_first_step(&blake2f_pre_step);
    ctx.pragma_last_step(&blake2f_final_step);

    ctx.pragma_num_steps(14);

    ctx.trace(move |ctx, values| {
        // println!("h_vec = {:x?}", values.h_vec.to_vec());
        // println!("m_vec = {:x?}", values.m_vec.to_vec());
        // println!("t0 = {:x?}, t1 = {:x?}", values.t0, values.t1);

        let h_vec_values = values.h_vec.to_vec();
        let m_vec_values = values.m_vec.to_vec();
        let iv_vec_values = IV_VALUES.to_vec();
        let mut v_vec_values = h_vec_values.clone();
        v_vec_values.append(&mut iv_vec_values.clone());

        let split_values = [
            IV_VALUES[4],
            values.t0,
            IV_VALUES[5],
            values.t1,
            IV_VALUES[6],
        ];
        let pre_inputs = PreInput {
            round: F::ZERO,
            t0: F::from(values.t0),
            t1: F::from(values.t1),
            f: F::from(if values.f { 1 } else { 0 }),
            h_vec: h_vec_values.iter().map(|&v| F::from(v)).collect(),
            m_vec: m_vec_values.iter().map(|&v| F::from(v)).collect(),
            iv_vec: iv_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_vec: v_vec_values.iter().map(|&v| F::from(v)).collect(),
            split_bit_vec: split_values
                .iter()
                .map(|&v| split_value(64, v as u128))
                .collect(),
        };
        ctx.add(&blake2f_pre_step, pre_inputs);

        v_vec_values[12] ^= values.t0;
        v_vec_values[13] ^= values.t1;
        if values.f {
            v_vec_values[14] ^= 0xFFFFFFFFFFFFFFFF;
        }

        for r in 0..values.round {
            let s = SIGMA_VALUES[(r as usize) % 10];

            let mut v_mid1_vec_values = v_vec_values.clone();
            let mut v_mid2_vec_values = v_vec_values.clone();
            let mut v_mid_va_bit_vec = Vec::new();
            let mut v_mid_vb_bit_vec = Vec::new();
            let mut v_mid_vc_bit_vec = Vec::new();
            let mut v_mid_vd_bit_vec = Vec::new();

            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (0, 4, 8, 12),
                (m_vec_values[s[0]], m_vec_values[s[1]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (1, 5, 9, 13),
                (m_vec_values[s[2]], m_vec_values[s[3]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (2, 6, 10, 14),
                (m_vec_values[s[4]], m_vec_values[s[5]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
                (3, 7, 11, 15),
                (m_vec_values[s[6]], m_vec_values[s[7]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );

            let mut v_mid3_vec_values = v_mid2_vec_values.clone();
            let mut v_mid4_vec_values = v_mid2_vec_values.clone();
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (0, 5, 10, 15),
                (m_vec_values[s[8]], m_vec_values[s[9]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (1, 6, 11, 12),
                (m_vec_values[s[10]], m_vec_values[s[11]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (2, 7, 8, 13),
                (m_vec_values[s[12]], m_vec_values[s[13]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
            );
            g_internal(
                (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
                (3, 4, 9, 14),
                (m_vec_values[s[14]], m_vec_values[s[15]]),
                &mut v_mid_va_bit_vec,
                &mut v_mid_vb_bit_vec,
                &mut v_mid_vc_bit_vec,
                &mut v_mid_vd_bit_vec,
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
            };
            ctx.add(&blake2f_g_step_vec[r as usize], ginputs);
            v_vec_values = v_mid4_vec_values.clone();
        }

        let output_vec_values: Vec<u64> = h_vec_values
            .iter()
            .zip(v_vec_values[0..8].iter().zip(v_vec_values[8..16].iter()))
            .map(|(h, (v1, v2))| h ^ v1 ^ v2)
            .collect();

        let final_inputs = FinalInput {
            round: F::from(values.round as u64),
            v_vec: v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_vec: h_vec_values.iter().map(|&v| F::from(v)).collect(),
            m_vec: m_vec_values.iter().map(|&v| F::from(v)).collect(),
            output_vec: output_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_split_bit_vec: v_vec_values
                .iter()
                .map(|&v| split_value(64, v as u128))
                .collect(),
            h_split_bit_vec: h_vec_values
                .iter()
                .map(|&v| split_value(64, v as u128))
                .collect(),
        };
        ctx.add(&blake2f_final_step, final_inputs);
        println!("output = {:?}", output_vec_values);
    })
}

fn blake2f_super_circuit<F: PrimeField + Hash>() -> SuperCircuit<F, InputValues> {
    super_circuit::<F, InputValues, _>("blake2f", |ctx| {
        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        let (_, iv_table) = ctx.sub_circuit(single_config, blake2f_iv_table, IV_LENGTH);

        let maxwidth_config = config(
            MaxWidthCellManager::new(2, true),
            SimpleStepSelectorBuilder {},
        );

        let params = CircuitParams { iv_table };
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

    let prover = MockProver::run(15, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();

    println!("result = {:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}
