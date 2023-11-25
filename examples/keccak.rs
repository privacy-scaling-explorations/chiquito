use chiquito::{
    ast::{query::Queriable, Expr},
    frontend::dsl::{lb::LookupTable, super_circuit, CircuitContext},
    plonkish::{
        backend::halo2::{chiquitoSuperCircuit2Halo2, ChiquitoHalo2SuperCircuit},
        compiler::{
            cell_manager::{MaxWidthCellManager, SingleRowCellManager},
            config,
            step_selector::SimpleStepSelectorBuilder,
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

pub const XOR_VALUE: [u64; NUM_BITS_PER_WORD] = [
    0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0,
    0x1, 0x0, 0x1, 0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1,
    0x0, 0x1, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x0, 0x1, 0x8,
    0x9, 0x8, 0x9, 0x8, 0x9, 0x8, 0x9,
];

pub const CHI_VALUE: [u64; NUM_BITS_PER_WORD] = [
    0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8, 0x9, 0x9, 0x8, 0x8, 0x8, 0x8, 0x8, 0x8, 0x9, 0x9,
    0x8, 0x8, 0x8, 0x8, 0x8, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0,
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

fn eval_threes<F: PrimeField<Repr = [u8; 32]>>() -> F {
    let threes_vec: [u8; NUM_BITS_PER_WORD] = [3; NUM_BITS_PER_WORD];
    convert_bits_to_f(&threes_vec.to_vec())
}

fn keccak_xor_table<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, ()>,
    lens: usize,
) -> LookupTable {
    use chiquito::frontend::dsl::cb::*;

    let lookup_xor_row: Queriable<F> = ctx.fixed("xor row");
    let lookup_xor_c: Queriable<F> = ctx.fixed("xor value");

    let constants_value = XOR_VALUE;
    assert_eq!(lens, constants_value.len());
    ctx.pragma_num_steps(lens);
    ctx.fixed_gen(move |ctx| {
        for (i, &value) in constants_value.iter().enumerate().take(lens) {
            ctx.assign(i, lookup_xor_row, F::from(i as u64));
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
            ctx.assign(i, lookup_chi_row, F::from(i as u64));
            ctx.assign(i, lookup_chi_c, F::from(value));
        }
    });

    ctx.new_table(table().add(lookup_chi_row).add(lookup_chi_c))
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


struct OneRoundValues<F>  {
    threes: F,
    round: F,
    round_cst: F,

    s_vec: Vec<F>,
    s_new_vec: Vec<F>,

    theta_split_vec: Vec<Vec<F>>,
    theta_split_xor_vec: Vec<Vec<F>>,
    // theta_sum_split_xor_value_vec: Vec<F>,
    // theta_sum_split_xor_move_value_vec: Vec<F>,
    theta_bit_0: Vec<F>,
    theta_bit_1: Vec<F>,
    theta_sum_split_vec: Vec<Vec<F>>,
    theta_sum_split_xor_vec: Vec<Vec<F>>,

    // rho_split_vec: Vec<Vec<F>>,
    rho_pi_s_new_vec: Vec<F>,
    rho_bit_0: Vec<F>,
    rho_bit_1: Vec<F>,

    chi_sum_value_vec: Vec<F>,
    chi_sum_split_value_vec: Vec<Vec<F>>,
    chi_split_value_vec: Vec<Vec<F>>,

    final_sum_split_vec: Vec<F>,
    final_xor_split_vec: Vec<F>,
}

fn eval_keccak_f_one_round<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(round: u64, cst: u64, s_vec: Vec<F>)-> OneRoundValues<F>{
    
    let mut s_new_vec = Vec::new();
    let mut theta_split_vec = Vec::new();
    let mut theta_split_xor_vec = Vec::new();
    let mut theta_sum_split_xor_value_vec = Vec::new();
    let mut theta_sum_split_xor_move_value_vec = Vec::new();
    let mut theta_bit_0 = Vec::new();
    let mut theta_bit_1 = Vec::new();
    let mut theta_sum_split_vec = Vec::new();
    let mut theta_sum_split_xor_vec = Vec::new();
    // let mut rho_split_vec = Vec::new();
    let mut rho_pi_s_new_vec = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut rho_bit_0 = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut rho_bit_1 = vec![F::ZERO; PART_SIZE * PART_SIZE];
    let mut chi_sum_value_vec= Vec::new();
    let mut chi_sum_split_value_vec = Vec::new();
    let mut chi_split_value_vec = Vec::new();
    let mut final_sum_split_vec = Vec::new();
    let mut final_xor_split_vec = Vec::new();

    let mut theta_st_bit_xor_vec = Vec::new();
    
    for i in 0..PART_SIZE {
        let sum = s_vec[i * PART_SIZE + 0] + s_vec[i * PART_SIZE + 1] + s_vec[i * PART_SIZE + 2] + s_vec[i * PART_SIZE + 3] + s_vec[i * PART_SIZE + 4];
        let sum_bits = convert_field_to_vec_bits(sum);

        let xor: F = field_xor(
            field_xor(field_xor(field_xor(s_vec[i * PART_SIZE + 0], s_vec[i * PART_SIZE + 1]), s_vec[i * PART_SIZE + 2]), s_vec[i * PART_SIZE + 3]),
            s_vec[i * PART_SIZE + 4],
        );
        let xor_bits = convert_field_to_vec_bits(xor);
        let mut xor_bits_move = xor_bits.clone();
        xor_bits_move.rotate_right(1);
        let xor_rot = convert_bits_to_f(&xor_bits_move);

        let mut sum_split = Vec::new();
        let mut sum_split_xor = Vec::new();
        for k in 0..sum_bits.len() / 2 {
            sum_split.push(
                F::from_u128(sum_bits[2 * k] as u128)
                    + F::from_u128(sum_bits[2 * k + 1] as u128) * F::from_u128(8),
            );
            sum_split_xor.push(
                F::from_u128(xor_bits[2 * k] as u128)
                    + F::from_u128(xor_bits[2 * k + 1] as u128) * F::from_u128(8),
            );
        }
        theta_split_vec.push(sum_split);
        theta_split_xor_vec.push(sum_split_xor);
        theta_sum_split_xor_value_vec.push(xor);
        theta_sum_split_xor_move_value_vec.push(xor_rot);
        theta_bit_0.push(F::from_u128(xor_bits[xor_bits.len() - 2] as u128));
        theta_bit_1.push(F::from_u128(xor_bits[xor_bits.len() - 1] as u128));
    }
    for i in 0..PART_SIZE {
        let xor = theta_sum_split_xor_value_vec[(i + PART_SIZE - 1) % PART_SIZE];
        let xor_rot = theta_sum_split_xor_move_value_vec[(i + 1) % PART_SIZE];
        for j in 0..PART_SIZE {
            let st = s_vec[i * PART_SIZE + j] + xor + xor_rot;
            let st_xor = field_xor(field_xor(s_vec[i * PART_SIZE + j], xor), xor_rot);
            let mut st_split = Vec::new();
            let mut st_split_xor = Vec::new();
            let st_bit_vec = convert_field_to_vec_bits(st);
            let st_bit_xor_vec = convert_field_to_vec_bits(st_xor);
            for i in 0..st_bit_vec.len() / 2 {
                st_split.push(
                    F::from_u128(st_bit_vec[2 * i] as u128)
                        + F::from_u128(st_bit_vec[2 * i + 1] as u128) * F::from_u128(8),
                );
                st_split_xor.push(F::from_u128(
                    st_bit_xor_vec[2 * i] as u128)
                    + F::from_u128(st_bit_xor_vec[2 * i + 1] as u128) * F::from_u128(8)
                );
            }
            theta_sum_split_vec.push(st_split);
            theta_sum_split_xor_vec.push(st_split_xor);
            // TODO: can be improved
            theta_st_bit_xor_vec.push(st_bit_xor_vec);
        }
    }
    
    // rho
    // a[x][y][z] = a[x][y][z-(t+1)(t+2)/2]
    let mut i = 0;
    let mut j = 0;
    for t in 0..PART_SIZE * PART_SIZE {
        if t == 0 {
            i = 0;
            j = 0;
        } else if t == 1 {
            i = 1;
            j = 0;
        } else {
            let m = j;
            j = (2 * i + 3 * j) % PART_SIZE;
            i = m;
        }
        let v = (t * (t + 1) / 2) % NUM_BITS_PER_WORD;

        let mut v_vec = theta_st_bit_xor_vec[i * PART_SIZE + j].clone();
        
        let mut b0 = F::ZERO;
        let mut b1 = F::ZERO;
        if v % 2 != 0 {
            b0 = F::from(v_vec[v_vec.len() - v - 1] as u64);
            b1 = F::from(v_vec[v_vec.len() - v] as u64);
        }
        
        v_vec.rotate_right(v);
        
        rho_bit_0[i*PART_SIZE + j] = b0;
        rho_bit_1[i*PART_SIZE + j] = b1;
        // pi
        // a[y][2x + 3y] = a[x][y]
        rho_pi_s_new_vec[j * PART_SIZE + ((2 * i + 3 * j) % PART_SIZE)] = convert_bits_to_f(&v_vec);
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
                .map(|(&a, (&b, &c))| 3 - 2 * a + b - c)
                .collect();
            let sum = convert_bits_to_f(&sum_vec);

            let split_chi_value: Vec<u8> = sum_vec
                .iter()
                .map(|&v| if v == 1 || v == 2 { 1 } else { 0 })
                .collect();
            let sum_chi = convert_bits_to_f(&split_chi_value);

            let sum_split_vec = (0..NUM_PER_WORD)
            .map(|i| {
                F::from_u128(sum_vec[2 * i] as u128 + sum_vec[2 * i + 1] as u128 * 8)
            }).collect();
            let chi_split_vec = (0..NUM_PER_WORD)
            .map(|i| {
                F::from_u128(split_chi_value[2 * i] as u128 + split_chi_value[2 * i + 1] as u128 * 8)
            }).collect();

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
    
    for i in 0..NUM_PER_WORD {
        final_sum_split_vec.push(xor_rows[2 * i].0 + xor_rows[2 * i + 1].0 * F::from_u128(8));
        final_xor_split_vec.push(xor_rows[2 * i].1 + xor_rows[2 * i + 1].1 * F::from_u128(8));
    }

    s_new_vec[0] = convert_bits_to_f(&split_xor_vec);

    OneRoundValues {

        threes: eval_threes(),
        round: F::from(round as u64),
        round_cst: pack_u64::<F>(cst),

        s_vec: s_vec.clone(),
        s_new_vec,

        theta_split_vec,
        theta_split_xor_vec,
        // theta_sum_split_xor_value_vec,
        // theta_sum_split_xor_move_value_vec,
        theta_bit_0,
        theta_bit_1,
        theta_sum_split_vec,
        theta_sum_split_xor_vec,

        // rho_split_vec,
        rho_pi_s_new_vec: rho_pi_s_new_vec,
        rho_bit_0,
        rho_bit_1,

        chi_sum_value_vec,
        chi_sum_split_value_vec,
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
    // 25
    let s_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE).map(|i|{ctx.forward(&format!("s[{}][{}]", i / PART_SIZE, i % PART_SIZE))}).collect();
    // 25
    let s_new_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE).map(|i|{ctx.forward(&format!("s[{}][{}]", i / PART_SIZE, i % PART_SIZE))}).collect();
    
    // 32
    let coeff_split_or_absorb_vec: Vec<Queriable<F>> = (0..NUM_PER_WORD)
        .map(|i| ctx.forward(&format!("coeff_split_{}", i)))
        .collect();

    let round: Queriable<F> = ctx.forward("round");
    let coeff64: Queriable<F> = ctx.forward("64");

    
    let keccak_first_step = ctx.step_type_def("keccak first step", |ctx| {
        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        let absorb_vec = coeff_split_or_absorb_vec.clone();
        let setup_absorb_vec = absorb_vec.clone();

        ctx.setup(move |ctx| {
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.constr(eq(setup_s_vec[i * PART_SIZE + j], 0));
                    if j * PART_SIZE + i < NUM_WORDS_TO_ABSORB {
                        // xor
                        // 000 xor 000/001 -> 000 + 000/001
                        ctx.transition(eq(
                            setup_s_vec[i * PART_SIZE + j] + setup_absorb_vec[i * PART_SIZE + j],
                            setup_s_vec[i * PART_SIZE + j].next(),
                        ));
                    } else {
                        ctx.transition(eq(setup_s_vec[i * PART_SIZE + j], setup_s_vec[i * PART_SIZE + j].next()));
                        ctx.constr(eq(setup_absorb_vec[i * PART_SIZE + j], 0));
                    }
                }
            }
            
            ctx.constr(eq(round, 0));
            ctx.transition(eq(round, round.next()));
        });

        ctx.wg::<(Vec<(F, F)>, F), _>(move |ctx, (absorb_rows, round_value)| {
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.assign(
                        absorb_vec[i * PART_SIZE + j],
                        absorb_rows[i * PART_SIZE + j].1,
                    );
                    ctx.assign(s_vec[i * PART_SIZE + j], F::ZERO);
                }
            }
            ctx.assign(round, round_value);
        })
    });
    
    let keccak_pre_step = ctx.step_type_def("keccak pre step", |ctx| {

        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        let s_new_vec = s_new_vec.clone();
        let setup_s_new_vec = s_new_vec.clone();

        let absorb_vec = coeff_split_or_absorb_vec.clone();
        let setup_absorb_vec = absorb_vec.clone();

        // 25
        let sum_split_value_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
            .map(|i| ctx.internal(&format!("sum_split_value_{}", i)))
            .collect();
        let setup_sum_split_value_vec = sum_split_value_vec.clone();

        let coeff_split_vec: Vec<Queriable<F>> = coeff_split_or_absorb_vec.clone();
        let setup_coeff_split_vec = coeff_split_vec.clone();

        // 17 * 32 = 544
        let split_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("split_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_split_vec = split_vec.clone();

        // 17 * 32 = 544
        let split_xor_vec: Vec<Vec<Queriable<F>>> = (0..NUM_WORDS_TO_ABSORB).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("split_xor_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_split_xor_vec = split_xor_vec.clone();

        ctx.setup(move |ctx| {
            ctx.constr(eq(setup_coeff_split_vec[0], 1));
            ctx.constr(eq(coeff64, 64));
            for k in 1..NUM_PER_WORD {
                ctx.constr(eq(
                    setup_coeff_split_vec[k - 1] * coeff64,
                    setup_coeff_split_vec[k],
                ));
            }

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    if j * PART_SIZE + i < NUM_WORDS_TO_ABSORB {
                        // xor
                        ctx.constr(eq(
                            setup_s_vec[i * PART_SIZE + j] + setup_absorb_vec[i * PART_SIZE + j],
                            setup_sum_split_value_vec[i * PART_SIZE + j],
                        ));
                        ctx.transition(eq(setup_s_new_vec[i * PART_SIZE + j], setup_s_vec[i * PART_SIZE + j].next()));
                    } else {
                        ctx.transition(eq(setup_s_vec[i * PART_SIZE + j], setup_s_vec[i * PART_SIZE + j].next()));
                        ctx.constr(eq(setup_absorb_vec[i * PART_SIZE + j], 0));
                    }
                }
            }
            
            for s in 0..NUM_WORDS_TO_ABSORB {
                
                // let s = (s % PART_SIZE) * PART_SIZE + s / PART_SIZE;
                for k in 0..NUM_PER_WORD {
                    ctx.add_lookup(
                        param
                            .xor_table
                            .apply(setup_split_vec[s][k])
                            .apply(setup_split_xor_vec[s][k]),
                    );
                }

                let mut sum_split_vec: Expr<F> = setup_split_vec[s][0] * setup_coeff_split_vec[0];
                let mut sum_split_xor_vec: Expr<F> =
                    setup_split_xor_vec[s][0] * setup_coeff_split_vec[0];
                for k in 1..NUM_PER_WORD {
                    sum_split_vec =
                        sum_split_vec + setup_split_vec[s][k] * setup_coeff_split_vec[k];
                    sum_split_xor_vec =
                        sum_split_xor_vec + setup_split_xor_vec[s][k] * setup_coeff_split_vec[k];
                }
                ctx.constr(eq(sum_split_vec, setup_sum_split_value_vec[s]));
                ctx.constr(eq(
                    sum_split_xor_vec,
                    setup_s_new_vec[s],
                ));
            }

            ctx.transition(eq(round, round.next()));
        });

        ctx.wg::<(Vec<(F, F, F)>, Vec<Vec<(F, F)>>, F), _>(move |ctx, (absorb_rows, split_values, round_value)| {

            // let coeff_split_vec
            // coeff64
            // round
            ctx.assign(coeff64, F::from_u128(64));
            let mut coeff_value = F::from_u128(1);
            for &coeff_split in coeff_split_vec.iter().take(NUM_PER_WORD) {
                ctx.assign(coeff_split, coeff_value);
                coeff_value *= F::from_u128(64)
            }
            ctx.assign(round, round_value);
            
            // let s_vec
            // let s_new_vec
            // let absorb_vec
            // let sum_split_value_vec
            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.assign(
                        sum_split_value_vec[i * PART_SIZE + j],
                        absorb_rows[i * PART_SIZE + j].0 + absorb_rows[i * PART_SIZE + j].1,
                    );
                    ctx.assign(
                        absorb_vec[i * PART_SIZE + j],
                        absorb_rows[i * PART_SIZE + j].1,
                    );
                    ctx.assign(s_vec[i * PART_SIZE + j], absorb_rows[i * PART_SIZE + j].0);
                    ctx.assign(s_new_vec[i * PART_SIZE + j], absorb_rows[i * PART_SIZE + j].2);
                }
            }

            // split_vec
            // split_xor_vec
            for i in 0..NUM_WORDS_TO_ABSORB {
                for j in 0..NUM_PER_WORD {
                    ctx.assign(split_vec[i][j],split_values[i][j].0);
                    ctx.assign(split_xor_vec[i][j],split_values[i][j].1);
                }
            };
        })

    });

    let keccak_one_round = ctx.step_type_def("keccak one round", |ctx|{
        // 32
        let coeff_split_vec: Vec<Queriable<F>> = coeff_split_or_absorb_vec.clone();
        let setup_coeff_split_vec = coeff_split_vec.clone();

        // 25
        let s_vec = s_vec.clone();
        let setup_s_vec = s_vec.clone();

        // 25
        let s_new_vec = s_new_vec.clone();
        let setup_s_new_vec = s_new_vec.clone();

        // 32 * 5
        let theta_split_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("theta_split_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_theta_split_vec = theta_split_vec.clone();

        // 32 * 5
        let theta_split_xor_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("split_xor_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_theta_split_xor_vec = theta_split_xor_vec.clone();

        // 5
        let theta_bit_0: Vec<Queriable<F>>= (0..PART_SIZE)
        .map(|i| ctx.internal(&format!("bit0_{}", i)))
        .collect();
        let setup_theta_bit_0 = theta_bit_0.clone();

        // 5
        let theta_bit_1: Vec<Queriable<F>> = (0..PART_SIZE)
        .map(|i| ctx.internal(&format!("bit1_{}", i)))
        .collect();
        let setup_theta_bit_1 = theta_bit_1.clone();

        // 25 * 32
        let theta_sum_split_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE)
        .map(|i| (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("sum_split_{}{}", i, j)))
            .collect())
        .collect();
        let setup_theta_sum_split_vec = theta_sum_split_vec.clone();

        // 25 * 32
        let theta_sum_split_xor_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE)
        .map(|i| (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("sum_split_xor_{}{}", i, j)))
            .collect())
        .collect();
        let setup_theta_sum_split_xor_vec = theta_sum_split_xor_vec.clone();

        // 25
        let rho_bit_0: Vec<Queriable<F>>= (0..PART_SIZE * PART_SIZE)
        .map(|i| ctx.internal(&format!("rho_bit0_{}", i)))
        .collect();
        let setup_rho_bit_0 = rho_bit_0.clone();

        // 25
        let rho_bit_1: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
        .map(|i| ctx.internal(&format!("rho_bit1_{}", i)))
        .collect();
        let setup_rho_bit_1 = rho_bit_1.clone();

        // 25
        let rho_pi_s_new_vec: Vec<Queriable<F>> =  (0..PART_SIZE * PART_SIZE).map(|i|{ctx.internal(&format!("rho_s[{}][{}]", i / PART_SIZE, i % PART_SIZE))}).collect();
        let setup_rho_pi_s_new_vec = rho_pi_s_new_vec.clone();

        // 3
        let round_cst: Queriable<F> = ctx.internal("round constant");
        let three2: Queriable<F> = ctx.internal("three2");
        let threes: Queriable<F> = ctx.internal("threes");

        // 25
        let chi_sum_value_vec: Vec<Queriable<F>> = (0..PART_SIZE * PART_SIZE)
        .map(|i| ctx.internal(&format!("chi_sum_value_{}", i)))
        .collect();
        let setup_chi_sum_value_vec: Vec<Queriable<F>> = chi_sum_value_vec.clone();

        // 25 * 32
        let chi_sum_split_value_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("chi_sum_split_value_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_chi_sum_split_value_vec: Vec<Vec<Queriable<F>>> = chi_sum_split_value_vec.clone();
        
        // 25 * 32
        let chi_split_value_vec: Vec<Vec<Queriable<F>>> = (0..PART_SIZE * PART_SIZE).map(|i|{
            (0..NUM_PER_WORD)
            .map(|j| ctx.internal(&format!("chi_split_value_{}_{}", i, j)))
            .collect()
        }).collect();
        let setup_chi_split_value_vec: Vec<Vec<Queriable<F>>> = chi_split_value_vec.clone();

        // 32
        let final_sum_split_vec: Vec<Queriable<F>> = (0..NUM_PER_WORD)
        .map(|i| ctx.internal(&format!("final_sum_split_{}", i)))
        .collect();
        let setup_final_sum_split_vec  = final_sum_split_vec.clone();

        // 32
        let final_xor_split_vec: Vec<Queriable<F>> = (0..NUM_PER_WORD)
        .map(|i| ctx.internal(&format!("final_xor_split_{}", i)))
        .collect();
        let setup_final_xor_split_vec  = final_xor_split_vec.clone();

        ctx.setup(move |ctx| {
            
            ctx.constr(eq(setup_coeff_split_vec[0], 1));
            ctx.constr(eq(coeff64, 64));
            for k in 1..NUM_PER_WORD {
                ctx.constr(eq(
                    setup_coeff_split_vec[k - 1] * coeff64,
                    setup_coeff_split_vec[k],
                ));
            }

            // Theta
            let mut theta_sum_split_xor_vec: Vec<Expr<F>> = Vec::new();
            let mut theta_sum_move_split_xor_vec: Vec<Expr<F>> = Vec::new();
            for s in 0..PART_SIZE {
                // 1. \sum_y' a[x][y'][z]
                // 2. xor(sum)
                let mut sum_split_vec: Expr<F> = setup_theta_split_vec[s][0] * setup_coeff_split_vec[0];
                let mut sum_split_xor_vec: Expr<F> = setup_theta_split_xor_vec[s][0] * setup_coeff_split_vec[0];
                for k in 1..NUM_PER_WORD {
                    sum_split_vec =
                        sum_split_vec + setup_theta_split_vec[s][k] * setup_coeff_split_vec[k];
                    sum_split_xor_vec =
                        sum_split_xor_vec + setup_theta_split_xor_vec[s][k] * setup_coeff_split_vec[k];
                }

                for k in 0..NUM_PER_WORD {
                    ctx.add_lookup(
                        param
                            .xor_table
                            .apply(setup_theta_split_vec[s][k])
                            .apply(setup_theta_split_xor_vec[s][k]),
                    );
                }

                ctx.constr(eq(
                    setup_s_vec[s * PART_SIZE + 0]
                        + setup_s_vec[s * PART_SIZE + 1]
                        + setup_s_vec[s * PART_SIZE + 2]
                        + setup_s_vec[s * PART_SIZE + 3]
                        + setup_s_vec[s * PART_SIZE + 4],
                    sum_split_vec,
                ));

                ctx.constr(eq(setup_theta_bit_0[s] * (setup_theta_bit_0[s] - 1), 0));
                ctx.constr(eq(setup_theta_bit_1[s] * (setup_theta_bit_1[s] - 1), 0));
                ctx.constr(eq(setup_theta_bit_0[s] + setup_theta_bit_1[s] * 8, setup_theta_split_xor_vec[s][NUM_PER_WORD - 1]));
                let sum_split_xor_move_value_vec = (sum_split_xor_vec.clone() - setup_theta_bit_1[s] * setup_coeff_split_vec[NUM_PER_WORD - 1] * 8) * 8 + setup_theta_bit_1[s];
                theta_sum_split_xor_vec.push(sum_split_xor_vec);
                theta_sum_move_split_xor_vec.push(sum_split_xor_move_value_vec);
            }

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
                    }  else {
                        let m = j;
                        j = (2 * i + 3 * j) % 5;
                        i = m;
                    }
                    t_vec[i * PART_SIZE + j] = t;
                }
            }

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    // Theta
                    // 3. a[x][y][z] = a[x][y][z] + xor(\sum_y' a[x-1][y'][z]) + xor(\sum a[x+1][y'][z-1])
                    // 4. xor(a[x][y][z])
                    for k in 0..NUM_PER_WORD {
                        ctx.add_lookup(
                            param
                                .xor_table
                                .apply(setup_theta_sum_split_vec[i * PART_SIZE + j][k])
                                .apply(setup_theta_sum_split_xor_vec[i * PART_SIZE + j][k]),
                        );
                    }
                    let mut theta_sum_split: Expr<F> = setup_theta_sum_split_vec[i * PART_SIZE + j][0] * setup_coeff_split_vec[0];
                    for k in 1..NUM_PER_WORD {
                        theta_sum_split =
                            theta_sum_split + setup_theta_sum_split_vec[i * PART_SIZE + j][k] * setup_coeff_split_vec[k];
                    }
                    ctx.constr(eq(
                        theta_sum_split,
                        setup_s_vec[i * PART_SIZE + j]
                            + theta_sum_split_xor_vec[(i + PART_SIZE - 1) % PART_SIZE].clone()
                            + theta_sum_move_split_xor_vec[(i + 1) % PART_SIZE].clone(),
                    ));

                    // rho
                    // a[x][y][z] = a[x][y][z-(t+1)(t+2)/2]
                    let v = ((t_vec[i * PART_SIZE + j] + 1) * t_vec[i * PART_SIZE + j] / 2) % NUM_BITS_PER_WORD;
                    let mut rho_sum_split_move_vec: Expr<F>; 
                    if v % 2 != 0  {
                        rho_sum_split_move_vec = setup_rho_bit_1[i * PART_SIZE + j] + setup_rho_bit_0[i * PART_SIZE + j] * setup_coeff_split_vec[NUM_PER_WORD - 1] * 8;
                        for k in 1..NUM_PER_WORD {
                            rho_sum_split_move_vec = rho_sum_split_move_vec + setup_theta_sum_split_xor_vec[i * PART_SIZE + j][(k - 1 + NUM_PER_WORD - (v - 1)/2) % NUM_PER_WORD] * setup_coeff_split_vec[k-1] * 8;
                        }
                        ctx.constr(eq(setup_rho_bit_0[i * PART_SIZE + j] * (setup_rho_bit_0[i * PART_SIZE + j] - 1), 0));
                        ctx.constr(eq(setup_rho_bit_1[i * PART_SIZE + j] * (setup_rho_bit_1[i * PART_SIZE + j] - 1), 0));
                        ctx.constr(eq(setup_rho_bit_0[i * PART_SIZE + j] + setup_rho_bit_1[i * PART_SIZE + j] * 8, setup_theta_sum_split_xor_vec[i * PART_SIZE + j][(NUM_PER_WORD - (v + 1)/2) % NUM_PER_WORD]));
                        
                    } else {
                        rho_sum_split_move_vec= setup_theta_sum_split_xor_vec[i * PART_SIZE + j][(NUM_PER_WORD - v/2) % NUM_PER_WORD] * setup_coeff_split_vec[0];
                        for k in 1..NUM_PER_WORD {
                            rho_sum_split_move_vec = rho_sum_split_move_vec + setup_theta_sum_split_xor_vec[i * PART_SIZE + j][(k + NUM_PER_WORD - v/2) % NUM_PER_WORD] * setup_coeff_split_vec[k];
                        }
                    }

                    // pi
                    // a[y][2x + 3y] = a[x][y]
                    ctx.constr(eq(rho_sum_split_move_vec, setup_rho_pi_s_new_vec[j * PART_SIZE + ((2 * i + 3 * j) % PART_SIZE)]));
                }    
            }

            // chi
            // a[x] = a[x] ^ (~a[x+1] & a[x+2])
            // todo: setup_rho_pi_s_new_vec can be remove
            ctx.constr(eq(three2, 27));
            let mut three_sum_split_vec: Expr<F> = three2 * 64 + three2;
            for _ in 2..NUM_PER_WORD {
                three_sum_split_vec = three_sum_split_vec * 64 + three2;
            }
            ctx.constr(eq(three_sum_split_vec, threes));
            ctx.add_lookup(param.constants_table.apply(round).apply(round_cst));

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.constr(eq(
                        threes - setup_rho_pi_s_new_vec[i * PART_SIZE + j] - setup_rho_pi_s_new_vec[i * PART_SIZE + j]
                            + setup_rho_pi_s_new_vec[((i + 1) % 5) * PART_SIZE + j]
                            - setup_rho_pi_s_new_vec[((i + 2) % 5)* PART_SIZE + j],
                            setup_chi_sum_value_vec[i * PART_SIZE + j],
                    ));
                    for k in 0..NUM_PER_WORD{
                        ctx.add_lookup(param.chi_table.apply(setup_chi_sum_split_value_vec[i * PART_SIZE + j][k]).apply(setup_chi_split_value_vec[i * PART_SIZE + j][k]));
                    }
    
                    let mut sum_split_vec: Expr<F> = setup_chi_sum_split_value_vec[i * PART_SIZE + j][0] * setup_coeff_split_vec[0];
                    let mut sum_split_chi_vec: Expr<F> = setup_chi_split_value_vec[i * PART_SIZE + j][0] * setup_coeff_split_vec[0];
                    for k in 1..NUM_PER_WORD {
                        sum_split_vec = sum_split_vec + setup_chi_sum_split_value_vec[i * PART_SIZE + j][k] * setup_coeff_split_vec[k];
                        sum_split_chi_vec = sum_split_chi_vec + setup_chi_split_value_vec[i * PART_SIZE + j][k] * setup_coeff_split_vec[k];
                    }
                    ctx.constr(eq(sum_split_vec, setup_chi_sum_value_vec[i * PART_SIZE + j]));
                    if i != 0 || j != 0 {
                        ctx.constr(eq(sum_split_chi_vec, setup_s_new_vec[i * PART_SIZE + j]));
                    } else {
                        let mut sum_s_split_vec: Expr<F> =
                        setup_final_sum_split_vec[0] * setup_coeff_split_vec[0];
                        let mut sum_s_split_xor_vec: Expr<F> =
                        setup_final_xor_split_vec[0] * setup_coeff_split_vec[0];
                        for k in 1..NUM_PER_WORD {
                            sum_s_split_vec =
                                sum_s_split_vec + setup_final_sum_split_vec[k] * setup_coeff_split_vec[k];
                            sum_s_split_xor_vec =
                                sum_s_split_xor_vec + setup_final_xor_split_vec[k] * setup_coeff_split_vec[k];
                        }
                        ctx.constr(eq(sum_s_split_vec, sum_split_chi_vec + round_cst));
                        ctx.constr(eq(sum_s_split_xor_vec, setup_s_new_vec[i * PART_SIZE + j]));
                    }
                }
            }

            ctx.transition(eq((round + 1 - round.next()) * (round + 1 - NUM_ROUNDS), 0));

            for i in 0..PART_SIZE {
                for j in 0..PART_SIZE {
                    ctx.transition(eq(setup_s_new_vec[i * PART_SIZE + j], setup_s_vec[i * PART_SIZE + j].next()));
                }
            }
        });

        ctx.wg::<OneRoundValues<F>, _>(move |ctx, values| {

            ctx.assign(coeff64, F::from_u128(64));
            ctx.assign(three2, F::from_u128(27));
            ctx.assign(threes, values.threes);
            ctx.assign(round, values.round);
            ctx.assign(round_cst, values.round_cst);
           
            let mut coeff_value = F::from_u128(1);
            for &coeff_split in coeff_split_vec.iter().take(NUM_PER_WORD) {
                ctx.assign(coeff_split, coeff_value);
                coeff_value *= F::from_u128(64);
            }
            for (q,v) in s_vec.iter().zip(values.s_vec.iter()) {
                ctx.assign(*q,*v)
            }
            for (q,v) in s_new_vec.iter().zip(values.s_new_vec.iter()) {
                ctx.assign(*q,*v)
            }
            for (q_vec, v_vec) in theta_split_vec.iter().zip(values.theta_split_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q_vec, v_vec) in theta_split_xor_vec.iter().zip(values.theta_split_xor_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q,v) in theta_bit_0.iter().zip(values.theta_bit_0.iter()) {
                ctx.assign(*q,*v)
            }
            for (q,v) in theta_bit_1.iter().zip(values.theta_bit_1.iter()) {
                ctx.assign(*q,*v)
            }
            for (q_vec, v_vec) in theta_sum_split_vec.iter().zip(values.theta_sum_split_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q_vec, v_vec) in theta_sum_split_xor_vec.iter().zip(values.theta_sum_split_xor_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q,v) in rho_bit_0.iter().zip(values.rho_bit_0.iter()) {
                ctx.assign(*q,*v)
            }
            for (q,v) in rho_bit_1.iter().zip(values.rho_bit_1.iter()) {
                ctx.assign(*q,*v)
            }
            for (q,v) in rho_pi_s_new_vec.iter().zip(values.rho_pi_s_new_vec.iter()) {
                ctx.assign(*q,*v)
            }
            
            for (q,v) in chi_sum_value_vec.iter().zip(values.chi_sum_value_vec.iter()) {
                ctx.assign(*q,*v)
            }
            for (q_vec, v_vec) in chi_sum_split_value_vec.iter().zip(values.chi_sum_split_value_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q_vec, v_vec) in chi_split_value_vec.iter().zip(values.chi_split_value_vec.iter()) {
                for (q,v) in q_vec.iter().zip(v_vec.iter()) {
                    ctx.assign(*q,*v)
                }
            }
            for (q,v) in final_sum_split_vec.iter().zip(values.final_sum_split_vec.iter()) {
                ctx.assign(*q,*v)
            }
            for (q,v) in final_xor_split_vec.iter().zip(values.final_xor_split_vec.iter()) {
                ctx.assign(*q,*v)
            }
        })
    });

    ctx.pragma_first_step(&keccak_first_step);
    ctx.pragma_last_step(&keccak_one_round);

    ctx.pragma_num_steps(param.step_num);

    ctx.trace(move |ctx, params| {
        let mut bits = params.bits.clone();
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

            if k == 0 {
                let absorb_rows: Vec<(F, F)> = (0..PART_SIZE * PART_SIZE)
                    .map(|idx| {
                        (
                            s[idx],
                            absorbs[(idx % PART_SIZE) * PART_SIZE + (idx / PART_SIZE)],
                        )
                    })
                    .collect();
                ctx.add(&keccak_first_step, (absorb_rows, F::ZERO));
            } else {
                let absorb_rows: Vec<(F, F, F)> = (0..PART_SIZE * PART_SIZE)
                    .map(|idx| {
                        (
                            s[idx],
                            absorbs[(idx % PART_SIZE) * PART_SIZE + (idx / PART_SIZE)],
                            s_new[idx],
                        )
                    })
                    .collect();
                let split_values = (0..NUM_WORDS_TO_ABSORB).map(|t|{
                    {
                        let i = t % PART_SIZE;
                        let j = t / PART_SIZE;
                        let v = i * PART_SIZE + j;
                        let (xor_rows, _, _) = eval_keccak_f_to_bit_vec::<F>(
                            absorb_rows[v].0 + absorb_rows[v].1,
                            absorb_rows[v].2,
                        );
                        xor_rows
                    }
                }).collect();
                ctx.add(&keccak_pre_step, (absorb_rows, split_values, F::ZERO)); 
            }

            for (round, &cst) in ROUND_CST.iter().enumerate().take(NUM_ROUNDS) {
                let values = eval_keccak_f_one_round(round as u64, cst, s_new.to_vec());
                
                s_new = values.s_new_vec.clone().try_into().unwrap();
                ctx.add(&keccak_one_round, values);
            }
        }

        // squeezing
        let mut output: Vec<F> = (0..NUM_WORDS_TO_ABSORB)
            .map(|k| {
                let i = k % PART_SIZE;
                let j = k / PART_SIZE;
                s_new[i* PART_SIZE + j]
            })
            .collect();

        for _ in 0..(params.output_len - 1) / RATE_IN_BITS {
            for (round, &cst) in ROUND_CST.iter().enumerate().take(NUM_ROUNDS) {
                let values = eval_keccak_f_one_round(round as u64, cst, s_new.to_vec());
                s_new = values.s_new_vec.clone().try_into().unwrap();
                ctx.add(&keccak_one_round, values);
            }
            let mut z_vec: Vec<F> = (0..NUM_WORDS_TO_ABSORB)
                .map(|k| s_new[(k % PART_SIZE) * PART_SIZE + k / PART_SIZE])
                .collect();
            output.append(&mut z_vec);
        }

        let mut output_bits: Vec<u8> = Vec::new();
        for out in output {
            let mut out_bits = convert_field_to_vec_bits(out);
            output_bits.append(&mut out_bits);
        }
        assert!(output_bits.len() >= params.output_len);
        output_bits = output_bits[0..params.output_len].to_vec();
        println!("output = {:?}", output_bits);
        // println!("num_steps = {:?}", ctx.num_steps);
    });
}

#[derive(Default)]
struct KeccakCircuit {
    pub bits: Vec<u8>,
    pub output_len: usize,
}

struct CircuitParams {
    pub constants_table: LookupTable,
    pub xor_table: LookupTable,
    pub chi_table: LookupTable,
    pub step_num: usize,
}

fn keccak_super_circuit<F: PrimeField<Repr = [u8; 32]> + Eq + Hash>(
    input_len: usize,
    output_len: usize,
) -> SuperCircuit<F, KeccakCircuit> {
    super_circuit::<F, KeccakCircuit, _>("keccak", |ctx| {
        let in_n = (input_len + 1 + RATE_IN_BITS) / RATE_IN_BITS;
        let out_n = output_len / RATE_IN_BITS;
        // let step_num = in_n
        //     * (1  + (NUM_ROUNDS) * ((25 + 5) + (25) + (25 + 1)))
        //     + out_n * ((NUM_ROUNDS) * ((25 + 5) + (25) + (25 + 1)));
        // println!("step_num = {}", step_num);
        let step_num = in_n * (1  + NUM_ROUNDS) + out_n * NUM_ROUNDS;

        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        let (_, constants_table) = ctx.sub_circuit(
            single_config.clone(),
            keccak_round_constants_table,
            NUM_ROUNDS + 1,
        );
        let (_, xor_table) =
            ctx.sub_circuit(single_config.clone(), keccak_xor_table, NUM_BITS_PER_WORD);
        let (_, chi_table) = ctx.sub_circuit(single_config, keccak_chi_table, NUM_BITS_PER_WORD);

        let params = CircuitParams {
            constants_table,
            xor_table,
            chi_table,
            step_num,
        };

        let maxwidth_config = config(
            MaxWidthCellManager::new(256
                , true),
            SimpleStepSelectorBuilder {},
        );
        let (keccak, _) = ctx.sub_circuit(maxwidth_config, keccak_circuit, params);

        ctx.mapping(move |ctx, values| {
            ctx.map(&keccak, values);
        })
    })
}

use chiquito::plonkish::backend::plaf::chiquito2Plaf;
use polyexen::plaf::{Witness, Plaf, PlafDisplayBaseTOML, PlafDisplayFixedCSV, WitnessDisplayCSV};

fn write_files(name: &str, plaf: &Plaf, wit: &Witness) -> Result<(), io::Error> {
    let mut base_file = File::create(format!("{}.toml", name))?;
    let mut fixed_file = File::create(format!("{}_fixed.csv", name))?;
    let mut witness_file = File::create(format!("{}_witness.csv", name))?;

    write!(base_file, "{}", PlafDisplayBaseTOML(plaf))?;
    write!(fixed_file, "{}", PlafDisplayFixedCSV(plaf))?;
    write!(witness_file, "{}", WitnessDisplayCSV(wit))?;
    Ok(())
}

fn keccak_plaf(circuit_param: KeccakCircuit, k: u32) {
    let super_circuit =
        keccak_super_circuit::<Fr>(circuit_param.bits.len(), circuit_param.output_len);
    let witness = super_circuit.get_mapping().generate(circuit_param);
    
    for wit_gen in witness.values(){
        let wit_gen = wit_gen.clone();

        let mut circuit = super_circuit.get_sub_circuits()[3].clone();
        circuit.columns.append(&mut super_circuit.get_sub_circuits()[0].columns);
        circuit.columns.append(&mut super_circuit.get_sub_circuits()[1].columns);
        circuit.columns.append(&mut super_circuit.get_sub_circuits()[2].columns);

        for (key, value) in super_circuit.get_sub_circuits()[0].fixed_assignments.iter(){
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[1].fixed_assignments.iter(){
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }
        for (key, value) in super_circuit.get_sub_circuits()[2].fixed_assignments.iter(){
            circuit.fixed_assignments.insert(key.clone(), value.clone());
        }

        let (plaf, plaf_wit_gen) = chiquito2Plaf(circuit, k, false);
        
        let mut plaf = plaf;
        plaf.set_challange_alias(0, "r_keccak".to_string());
        let wit = plaf_wit_gen.generate(Some(wit_gen));
        write_files("keccak", &plaf, &wit).unwrap();
        
    }
}

fn keccak_run(circuit_param: KeccakCircuit, k: u32){

    let super_circuit =
        keccak_super_circuit::<Fr>(circuit_param.bits.len(), circuit_param.output_len);
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
        bits: vec![0, 0, 0, 0, 0, 0, 0, 0],
        output_len: 256,
        // bits: vec![
        //     0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
        // 1,     1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
        // 1, 0, 1, 0,     1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,
        // 1, 0, 1, 1, 1, 1, 1,     0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,     0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
        // 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,     1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1,
        // 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,     1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
        // 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1,     1, 1, 1, 0, 0, 0, 0,
        // 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,     1, 0, 1, 0,
        // 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,     1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1,
        //     1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1,
        // 1,     1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
        // 0, 0, 0, 1,     0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1,
        // 1, 0, 1, 0, 1, 1, 0,     1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
        // 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,     1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
        // 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,     1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        // 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1,     0, 1, 0, 1, 0, 1, 1, 0, 1, 1,
        // 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,     1, 1, 1, 1, 0, 0, 0,
        // 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,     1, 0, 1, 1,
        // 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,     0,
        // 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0,
        //     0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,
        // 1,     0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1,
        // 0, 0, 0, 0,     0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,
        // 1, 0, 1, 0, 1, 1, 0,     1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,
        // 0, 1, 1, 1, 1, 1, 0, 0, 0, 0,     0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1,
        // 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1,     1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1,
        // 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,     0, 0, 0, 1, 0, 1, 1, 0, 1, 0,
        // 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,     1, 1, 0, 1, 1, 1, 1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,     0, 0, 0, 1,
        // 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,     1,
        // 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0,
        //     0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
        // 0,     1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,
        // 1, 1, 1, 0,     0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0,
        // 0, 0, 1, 0, 1, 1, 0,     1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        // 1, 0, 1, 1, 0, 1, 1, 1, 1, 1,     0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1,
        // 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1,     0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0,
        // 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,     0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
        // 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1,     0, 1, 1, 0, 1, 1, 1,
        // 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1,     0, 0, 0, 0,
        // 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1,     0,
        // 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
        //     1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,
        // 1,     0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,
        // 1, 1, 1, 1,     1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
        // 0, 0, 0, 1, 0, 1, 0,     1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1,
        // 0, 1, 0, 1, 1, 0, 1, 1, 1, 1,     1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0,
        // 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1,     1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,
        // 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1,     1, 1, 1, 0, 0, 0, 0, 0, 1, 0,
        // 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1,     0, 1, 0, 1, 0, 1, 1,
        // 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1,     1, 1, 1, 0,
        // 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,     1,
        // 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
        //     1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1,
        // 0,     1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0,
        // 1, 1, 0, 1,     1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1,
        // 1, 1, 0, 0, 0, 0, 0,     1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0,
        // 0, 1, 0, 1, 0, 1, 0, 1, 1, 0,     1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
        // 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,     1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,     1, 1, 1, 1, 0, 0, 0, 0, 0, 1,
        // 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1,     0, 1, 1, 0, 1, 0, 1,
        // 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0,     1, 1, 1, 1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0,     0,
        // 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1,
        //     1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
        // 0,     0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        // 1, 0, 1, 1,     0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1,
        // 1, 1, 1, 0, 0, 0, 0,     0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0,
        // 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,     0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
        // 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0,     0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
        // 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0,     1, 1, 0, 1, 1, 1, 1, 1, 0, 0,
        // 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,     0, 0, 0, 0, 1, 0, 1,
        // 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,     1, 1, 0, 1,
        // 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0,     0,
        // 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1,
        //     1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,
        // 0,     0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0,
        // 1, 1, 0, 1,     0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1,
        // 1, 0, 1, 1, 1, 1, 1,     0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1,
        // 1, 0, 0, 0, 0, 0, 1, 0, 1, ],
        // output_len: 20,
    };

    keccak_run(circuit_param, 14);
    // keccak_plaf(circuit_param, 11);
}

