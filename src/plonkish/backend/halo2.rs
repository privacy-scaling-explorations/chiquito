use std::{collections::HashMap, fs::File, hash::Hash, iter, marker::PhantomData, vec};

use halo2_backend::plonk::{
    keygen::{keygen_pk, keygen_vk},
    prover::ProverSingle,
    verifier::verify_proof_single,
    Error as ErrorBack,
};
use halo2_middleware::{
    circuit::{
        Any as Columns, Cell as CellMid, ColumnMid, CompiledCircuit, ExpressionMid, GateMid,
        Preprocessing, QueryMid, VarMid,
    },
    lookup,
    permutation::{self, AssemblyMid},
    zal::impls::{H2cEngine, PlonkEngineConfig},
};
use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        ff::PrimeField,
    },
    plonk::{Any, Column, ConstraintSystemMid, Error, ProvingKey, VerifyingKey},
    poly::{
        commitment::Params,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
        Rotation,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use rand_chacha::rand_core::{
    block::{BlockRng, BlockRngCore},
    OsRng,
};

use crate::{
    field::Field as ChiquitoField,
    plonkish::{
        compiler::PlonkishCompilationResult,
        ir::{
            assignments::Assignments,
            sc::{SuperAssignments, SuperCircuit},
            Circuit, Column as cColumn,
            ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
            PolyExpr,
        },
    },
    util::UUID,
    wit_gen::TraceGenerator,
};

impl<T: PrimeField + From<u64>> ChiquitoField for T {
    const ZERO: Self = <Self as Field>::ZERO;
    const ONE: Self = <Self as Field>::ONE;

    fn mi(&self) -> Self {
        self.invert().unwrap_or(Self::ZERO)
    }

    fn pow<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        Field::pow(self, exp)
    }

    fn from_big_int(value: &num_bigint::BigInt) -> Self {
        PrimeField::from_str_vartime(value.to_string().as_str()).expect("field value")
    }

    fn random(rng: impl rand_chacha::rand_core::RngCore) -> Self {
        Self::random(rng)
    }
}

trait Halo2Configurable<F: PrimeField> {
    fn compile_middleware(
        &mut self,
        num_circuit_rows: usize,
    ) -> Result<(CompiledCircuit<F>, u32), Error> {
        let mut cs_builder = self.configure_cs();

        let preprocessing = self.preprocessing(&mut cs_builder);

        let occupied_rows = num_circuit_rows + cs_builder.minimum_rows();
        let k = occupied_rows.next_power_of_two().trailing_zeros();
        let n = 2usize.pow(k);

        Ok((
            CompiledCircuit {
                cs: cs_builder.into(),
                preprocessing: preprocessing.extend(n),
            },
            k,
        ))
    }

    fn configure_cs(&mut self) -> ConstraintSystemBuilder<F>;
    fn preprocessing(&self, cs: &mut ConstraintSystemBuilder<F>) -> PreprocessingCompact<F>;
}

pub trait Halo2WitnessGenerator<F, W> {
    fn instance(&self, witness: &W) -> Vec<Vec<F>>;
    fn assigned_witness(
        &self,
        witness: &W,
        params_n: usize,
        num_advice_columns: usize,
    ) -> Vec<Option<Vec<F>>>;
}

#[derive(Clone, Debug)]
pub struct ChiquitoHalo2<F: PrimeField + From<u64>> {
    pub debug: bool,

    pub(crate) plonkish_ir: Circuit<F>,

    advice_columns: HashMap<UUID, ColumnMid>,
    fixed_columns: HashMap<UUID, ColumnMid>,

    ir_id: UUID,
}

impl<F: PrimeField + Hash> Halo2Configurable<F> for ChiquitoHalo2<F> {
    fn preprocessing(
        &self,
        cs_builder: &mut ConstraintSystemBuilder<F>,
    ) -> PreprocessingCompact<F> {
        let fixed_count = self.plonkish_ir.fixed_assignments.0.len();
        let mut fixed = vec![vec![]; fixed_count];

        for (column, values) in self.plonkish_ir.fixed_assignments.iter() {
            let column = cs_builder.convert_fixed_column(column);

            fixed[column.index].extend(values.iter().cloned());
        }

        let mut copies = vec![];
        cs_builder.collect_permutations(&mut copies, &self.plonkish_ir.exposed);

        PreprocessingCompact {
            permutation: AssemblyMid { copies },
            fixed_compact: fixed,
        }
    }

    fn configure_cs(&mut self) -> ConstraintSystemBuilder<F> {
        let mut cs_builder = ConstraintSystemBuilder::new();

        self.configure_halo2_columns(&mut cs_builder);

        cs_builder
    }
}

/// "Compact" preprocessing
/// Created before the circuit size is known (here the height of the fixed assignments is defined
/// only by the number of assigned values)
struct PreprocessingCompact<F: Field> {
    permutation: AssemblyMid,
    fixed_compact: Vec<Vec<F>>,
}

impl<F: Field> PreprocessingCompact<F> {
    /// Extend the preprocessing to the full circuit size
    fn extend(mut self, n: usize) -> Preprocessing<F> {
        self.fixed_compact
            .iter_mut()
            .for_each(|f| f.extend(iter::repeat(F::default()).take(n - f.len())));

        Preprocessing {
            permutation: self.permutation,
            fixed: self.fixed_compact,
        }
    }
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2<F> {
    pub fn new(circuit: Circuit<F>) -> ChiquitoHalo2<F> {
        let ir_id = circuit.id;
        ChiquitoHalo2 {
            debug: true,
            plonkish_ir: circuit,
            advice_columns: Default::default(),
            fixed_columns: Default::default(),
            ir_id,
        }
    }

    fn configure_halo2_columns(&mut self, meta: &mut ConstraintSystemBuilder<F>) {
        let mut advice_columns: HashMap<UUID, ColumnMid> = HashMap::new();
        let mut fixed_columns: HashMap<UUID, ColumnMid> = HashMap::new();

        self.plonkish_ir
            .columns
            .iter()
            .for_each(|column| match column.ctype {
                cAdvice => {
                    let halo2_column = meta.advice_column(column);
                    advice_columns.insert(column.uuid(), halo2_column);
                }
                cFixed => {
                    let halo2_column = meta.fixed_column(column);
                    fixed_columns.insert(column.uuid(), halo2_column);
                }
                Halo2Advice | Halo2Fixed => panic!(
                    "Use src/plonkish/backend/halo2_legacy.rs to compile a circuit with imported Halo2 columns"
                ),
            });

        if !self.plonkish_ir.exposed.is_empty() {
            meta.has_instance_column = true;
        }

        self.plonkish_ir.polys.iter().for_each(|poly| {
            meta.gates.push(GateMid {
                name: "main".to_string(),
                poly: meta.convert_poly(&poly.expr),
            })
        });

        for lookup in self.plonkish_ir.lookups.iter() {
            let annotation: &'static str = Box::leak(lookup.annotation.clone().into_boxed_str());
            let mut exprs = Vec::new();
            for (src, dest) in lookup.exprs.iter() {
                exprs.push((meta.convert_poly(src), meta.convert_poly(dest)))
            }
            meta.lookups.push(lookup::ArgumentMid {
                name: annotation.to_string(),
                input_expressions: exprs.iter().map(|(src, _)| src.clone()).collect(),
                table_expressions: exprs.iter().map(|(_, dest)| dest.clone()).collect(),
            });
        }

        self.advice_columns = advice_columns;
        self.fixed_columns = fixed_columns;
    }
}

impl<F: PrimeField> ConstraintSystemBuilder<F> {
    fn convert_poly(&self, src: &PolyExpr<F>) -> ExpressionMid<F> {
        match src {
            PolyExpr::Const(c, _) => ExpressionMid::Constant(*c),
            PolyExpr::Sum(es, _) => {
                let mut iter = es.iter();
                let first = self.convert_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.convert_poly(e))
            }
            PolyExpr::Mul(es, _) => {
                let mut iter = es.iter();
                let first = self.convert_poly(iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.convert_poly(e))
            }
            PolyExpr::Neg(e, _) => -self.convert_poly(e),
            PolyExpr::Pow(e, n, _) => {
                if *n == 0 {
                    ExpressionMid::Constant(F::ONE)
                } else {
                    let e = self.convert_poly(e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            PolyExpr::Halo2Expr(e, _) => ExpressionMid::from(e.clone()),
            PolyExpr::Query((column, rotation, _), _) => self.convert_query(column, *rotation),
            PolyExpr::MI(_, _) => panic!("mi elimination not done"),
        }
    }

    fn convert_query(&self, column: &cColumn, rotation: i32) -> ExpressionMid<F> {
        match column.ctype {
            cAdvice => ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index: self.advice_idx_map[&column.uuid()],
                column_type: Any::Advice,
                rotation: Rotation(rotation),
            })),
            cFixed => ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index: self.fixed_idx_map[&column.uuid()],
                column_type: Any::Fixed,
                rotation: Rotation(rotation),
            })),
            Halo2Advice | Halo2Fixed => panic!(
                    "Use src/plonkish/backend/halo2_legacy.rs to compile a circuit with imported Halo2 columns"
                ),
        }
    }

    fn convert_advice_column(&self, column: &cColumn) -> ColumnMid {
        match column.ctype {
            cAdvice => ColumnMid {
                column_type: Columns::Advice,
                index: *self
                    .advice_idx_map
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            },
            Halo2Advice => panic!(
                    "Use src/plonkish/backend/halo2_legacy.rs to compile a circuit with imported Halo2 columns"
                ),
            _ => panic!("wrong column type"),
        }
    }

    fn convert_fixed_column(&self, column: &cColumn) -> ColumnMid {
        match column.ctype {
            cFixed  => ColumnMid {
                column_type: Columns::Fixed,
                index: *self
                    .fixed_idx_map
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            },
             Halo2Fixed => panic!(
                    "Use src/plonkish/backend/halo2_legacy.rs to compile a circuit with imported Halo2 columns"
                ),
            _ => panic!("wrong column type"),
        }
    }

    fn annotate(&mut self, index: usize, column: &cColumn, column_type: Any) {
        self.annotations
            .insert(ColumnMid { index, column_type }, column.annotation.clone());
    }

    fn count_query(&mut self, column: Column<Any>) {
        match column.column_type {
            Any::Advice => {
                let advice_queries = &mut self.advice_queries;
                *advice_queries.entry(column.index).or_insert(0) += 1;
            }
            Any::Fixed => {
                let fixed_queries = &mut self.fixed_queries;
                *fixed_queries.entry(column.index).or_insert(0) += 1;
            }
            Any::Instance => {
                let instance_queries = &mut self.instance_queries;
                *instance_queries.entry(column.index).or_insert(0) += 1;
            }
        }
    }

    /// Compute the minimum number of rows of the circuit.
    /// For constants explanation see https://github.com/privacy-scaling-explorations/halo2/blob/bc857a701715ac3608056cb9b1999ad7cbc00b59/halo2_frontend/src/plonk/circuit/constraint_system.rs#L1055
    fn minimum_rows(&self) -> usize {
        self.blinding_factors() + 3
    }

    /// Compute the number of blinding factors necessary to perfectly blind
    /// each of the prover's witness polynomials.
    /// For constants explanation see https://github.com/privacy-scaling-explorations/halo2/blob/main/halo2_frontend/src/plonk/circuit/constraint_system.rs#L1026
    pub(crate) fn blinding_factors(&self) -> usize {
        let factors = *self.advice_queries.values().max().unwrap_or(&1);
        let factors = std::cmp::max(3, factors);
        factors + 2
    }

    fn collect_permutations(
        &mut self,
        copies: &mut Vec<(CellMid, CellMid)>,
        exposed: &[(cColumn, i32)],
    ) {
        exposed
            .iter()
            .enumerate()
            .for_each(|(row, (column, offset))| {
                let col_type: Columns = match column.ctype {
                    cAdvice  => Columns::Advice,
                    cFixed  => Columns::Fixed,
                    Halo2Advice | Halo2Fixed => panic!(
                    "Use src/plonkish/backend/halo2_legacy.rs to compile a circuit with imported Halo2 columns"
                ),
                };

                let index = if col_type == Columns::Advice {
                    let column = self.convert_advice_column(column);
                    self.collect_permutation(column);
                    column.index
                } else {
                    let column = self.convert_fixed_column(column);
                    self.collect_permutation(column);
                    column.index
                };

                let column_mid = ColumnMid::new(col_type, index);

                let instance_column = ColumnMid::new(Columns::Instance, 0);
                self.collect_permutation(instance_column);
                copies.push((
                    CellMid {
                        column: column_mid,
                        row: *offset as usize,
                    },
                    CellMid {
                        column: instance_column,
                        row,
                    },
                ));
            });
    }

    fn collect_permutation<C: Into<Column<Any>>>(&mut self, column: C) {
        let column: Column<Any> = column.into();
        self.count_query(column);
        if !self.permutation.columns.contains(&ColumnMid {
            column_type: column.column_type,
            index: column.index,
        }) {
            self.permutation = PermutationArgument {
                columns: self
                    .permutation
                    .columns
                    .iter()
                    .cloned()
                    .chain(iter::once(ColumnMid {
                        column_type: column.column_type,
                        index: column.index,
                    }))
                    .collect(),
            };
        }
    }

    fn new() -> Self {
        Self::default()
    }

    fn advice_column(&mut self, column: &cColumn) -> ColumnMid {
        let index = self.num_advice_columns;
        self.allocate_advice(index, column)
    }

    fn fixed_column(&mut self, column: &cColumn) -> ColumnMid {
        let index = self.num_fixed_columns;
        self.allocate_fixed(index, column)
    }

    fn allocate_fixed(&mut self, index: usize, column: &cColumn) -> ColumnMid {
        let column_mid = ColumnMid {
            column_type: Any::Fixed,
            index,
        };
        self.fixed_idx_map.insert(column.uuid(), index);
        self.annotate(index, column, Any::Fixed);
        self.num_fixed_columns += 1;
        column_mid
    }

    fn allocate_advice(&mut self, index: usize, column: &cColumn) -> ColumnMid {
        let column_mid = ColumnMid {
            column_type: Any::Advice,
            index,
        };
        self.advice_idx_map.insert(column.uuid(), index);
        self.annotate(index, column, Any::Advice);
        self.num_advice_columns += 1;
        column_mid
    }
}

impl<F: PrimeField> Halo2WitnessGenerator<F, Assignments<F>> for ChiquitoHalo2<F> {
    fn instance(&self, witness: &Assignments<F>) -> Vec<Vec<F>> {
        if !self.plonkish_ir.exposed.is_empty() {
            vec![self.plonkish_ir.instance(witness)]
        } else {
            vec![]
        }
    }

    fn assigned_witness(
        &self,
        witness: &Assignments<F>,
        params_n: usize,
        num_advice_columns: usize,
    ) -> Vec<Option<Vec<F>>> {
        let mut assigned_witness = vec![Some(vec![F::default(); params_n]); num_advice_columns];

        assign_witness(self, witness, &mut assigned_witness);

        assigned_witness
    }
}

#[derive(Clone, Debug, Default)]
pub struct ChiquitoHalo2SuperCircuit<F: PrimeField + From<u64>> {
    sub_circuits: Vec<ChiquitoHalo2<F>>,
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2SuperCircuit<F> {
    fn new(sub_circuits: Vec<ChiquitoHalo2<F>>) -> Self {
        Self { sub_circuits }
    }
}

impl<F: PrimeField> Halo2WitnessGenerator<F, SuperAssignments<F>> for ChiquitoHalo2SuperCircuit<F> {
    fn instance(&self, witness: &SuperAssignments<F>) -> Vec<Vec<F>> {
        let mut instance = Vec::new();

        for circuit in self.sub_circuits.iter() {
            if !circuit.plonkish_ir.exposed.is_empty() {
                let instance_values = circuit.plonkish_ir.instance(
                    witness
                        .get(&circuit.ir_id)
                        .expect("No matching witness found for given UUID."),
                );
                instance.push(instance_values);
            }
        }

        instance
    }

    fn assigned_witness(
        &self,
        witness: &SuperAssignments<F>,
        params_n: usize,
        num_advice_columns: usize,
    ) -> Vec<Option<Vec<F>>> {
        let mut assigned_witness = vec![Some(vec![F::default(); params_n]); num_advice_columns];

        for circuit in self.sub_circuits.iter() {
            if let Some(assignments) = witness.get(&circuit.ir_id) {
                assign_witness(circuit, assignments, &mut assigned_witness);
            }
        }

        assigned_witness
    }
}

impl<F: PrimeField + Hash> Halo2Configurable<F> for ChiquitoHalo2SuperCircuit<F> {
    fn configure_cs(&mut self) -> ConstraintSystemBuilder<F> {
        let mut cs_builder = ConstraintSystemBuilder::new();

        self.sub_circuits
            .iter_mut()
            .for_each(|c| c.configure_halo2_columns(&mut cs_builder));

        let advice_columns: HashMap<UUID, ColumnMid> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.advice_columns.clone());
                    acc
                });
        let fixed_columns: HashMap<UUID, ColumnMid> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.fixed_columns.clone());
                    acc
                });

        self.sub_circuits.iter_mut().for_each(|sub_circuit| {
            sub_circuit.advice_columns = advice_columns.clone();
            sub_circuit.fixed_columns = fixed_columns.clone();
        });

        cs_builder
    }

    fn preprocessing(
        &self,
        cs_builder: &mut ConstraintSystemBuilder<F>,
    ) -> PreprocessingCompact<F> {
        let fixed_columns: HashMap<UUID, ColumnMid> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.fixed_columns.clone());
                    acc
                });

        let fixed_count = fixed_columns.len();
        let mut fixed = vec![vec![]; fixed_count];

        let mut copies = vec![];
        for subcircuit in self.sub_circuits.iter() {
            for (column, values) in subcircuit.plonkish_ir.fixed_assignments.iter() {
                let column = fixed_columns.get(&column.uuid()).unwrap();

                fixed[column.index].extend(values.iter().cloned());
            }
            cs_builder.collect_permutations(&mut copies, &subcircuit.plonkish_ir.exposed);
        }

        PreprocessingCompact {
            permutation: AssemblyMid { copies },
            fixed_compact: fixed,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct PermutationArgument {
    /// A sequence of columns involved in the argument.
    pub columns: Vec<ColumnMid>,
}

#[derive(Default)]
struct ConstraintSystemBuilder<F: PrimeField> {
    num_fixed_columns: usize,
    num_advice_columns: usize,
    has_instance_column: bool,
    gates: Vec<GateMid<F>>,
    lookups: Vec<lookup::ArgumentMid<F>>,
    /// Map from advice column UUID to index
    advice_idx_map: HashMap<UUID, usize>,
    /// Map from fixed column UUID to index
    fixed_idx_map: HashMap<UUID, usize>,
    permutation: PermutationArgument,
    advice_queries: HashMap<usize, usize>,
    fixed_queries: HashMap<usize, usize>,
    instance_queries: HashMap<usize, usize>,
    annotations: HashMap<ColumnMid, String>,
}

impl<F: PrimeField> From<ConstraintSystemBuilder<F>> for ConstraintSystemMid<F> {
    fn from(val: ConstraintSystemBuilder<F>) -> Self {
        ConstraintSystemMid {
            num_fixed_columns: val.num_fixed_columns,
            num_advice_columns: val.num_advice_columns,
            num_instance_columns: if val.has_instance_column { 1 } else { 0 },
            num_challenges: 0,
            unblinded_advice_columns: Vec::new(),
            advice_column_phase: (0..val.num_advice_columns).map(|_| 0).collect(),
            challenge_phase: Vec::new(),
            gates: val.gates,
            permutation: permutation::ArgumentMid {
                columns: val.permutation.columns,
            },
            lookups: val.lookups,
            shuffles: Vec::new(),
            general_column_annotations: val.annotations,
            minimum_degree: None,
        }
    }
}

/// Verify Halo2 proof
/// ### Arguments
/// * `proof` - Halo2 proof
/// * `params` - KZG parameters
/// * `vk` - Verifying key
/// * `instance` - circuit instance values
/// ### Returns
/// * `Ok(())` if the proof is valid
/// * `Err(ErrorBack)` if the proof is invalid
pub fn halo2_verify(
    proof: Vec<u8>,
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    instance: Vec<Vec<Fr>>,
) -> Result<(), ErrorBack> {
    // Verify
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&verifier_params);

    let result = verify_proof_single::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, _, _, _>(
        &verifier_params,
        vk,
        strategy,
        instance,
        &mut verifier_transcript,
    );
    result
}

/// Halo2 setup
struct Setup {
    cs: ConstraintSystemMid<Fr>,
    params: ParamsKZG<Bn256>,
    vk: VerifyingKey<G1Affine>,
    pk: ProvingKey<G1Affine>,
}

/// Halo2 prover
pub struct Halo2Prover<F, W, WG>
where
    WG: Halo2WitnessGenerator<F, W>,
{
    setup: Setup,
    wit_gen: WG,

    _p: PhantomData<(F, W)>,
}

impl<W, WG: Halo2WitnessGenerator<Fr, W>> Halo2Prover<Fr, W, WG> {
    fn new(setup: Setup, wit_gen: WG) -> Halo2Prover<Fr, W, WG> {
        Halo2Prover {
            setup,
            wit_gen,
            _p: PhantomData,
        }
    }

    /// Generate halo2 proof.
    pub fn generate_proof(&self, witness: W) -> (Vec<u8>, Vec<Vec<Fr>>) {
        let instance = self.wit_gen.instance(&witness);

        // Proving
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        let mut prover = create_prover(&self.setup, &instance, &mut transcript);

        for phase in 0..self.setup.cs.phases() {
            let assigned_witness = self.wit_gen.assigned_witness(
                &witness,
                self.setup.params.n() as usize,
                self.setup.cs.num_advice_columns,
            );

            // TODO ignoring the challenges produced by the phase, but can they be useful later?
            let _ = prover.commit_phase(phase as u8, assigned_witness).unwrap();
        }
        prover.create_proof().unwrap();
        let proof = transcript.finalize();

        (proof, instance)
    }

    /// Get halo2 setup params
    pub fn get_params(&self) -> &ParamsKZG<Bn256> {
        &self.setup.params
    }

    /// Get halo2 verifying key
    pub fn get_vk(&self) -> &VerifyingKey<G1Affine> {
        &self.setup.vk
    }

    /// Get halo2 proving key
    pub fn get_pk(&self) -> &ProvingKey<G1Affine> {
        &self.setup.pk
    }

    pub fn get_k(&self) -> u32 {
        self.setup.params.k()
    }
}

#[allow(clippy::type_complexity)]
fn create_prover<'a>(
    setup: &'a Setup,
    instance: &[Vec<Fr>],
    transcript: &'a mut Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
) -> ProverSingle<
    'a,
    'a,
    KZGCommitmentScheme<Bn256>,
    ProverSHPLONK<'a, Bn256>,
    Challenge255<G1Affine>,
    OsRng,
    Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
    H2cEngine,
> {
    ProverSingle::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            _,
            _,
            _,
            _,
        >::new_with_engine(
            PlonkEngineConfig::new()
                        .set_curve::<G1Affine>()
                        .set_msm(H2cEngine::new())
                        .build(),
            &setup.params,
            &setup.pk,
            instance.to_vec(),
            OsRng, // this rng is used by the prover to generate blinding factors
            transcript,
        )
        .unwrap()
}

fn assign_witness<F: PrimeField + From<u64>>(
    circuit: &ChiquitoHalo2<F>,
    witness: &Assignments<F>,
    assigned_witness: &mut [Option<Vec<F>>],
) {
    for (column, values) in witness.iter() {
        let circuit_column = circuit.advice_columns.get(&column.uuid()).unwrap();
        let halo2_column = Column::<Any>::from(*circuit_column);
        for (offset, value) in values.iter().enumerate() {
            assigned_witness[halo2_column.index].as_mut().unwrap()[offset] = *value;
        }
    }
}

pub trait Halo2Provable<W, WG: Halo2WitnessGenerator<Fr, W>> {
    /// Create a Halo2 prover
    ///
    /// ### Arguments
    /// * `params_path` - path to trusted setup file
    ///
    /// ### Returns
    /// * a Halo2 prover
    fn create_halo2_prover(&mut self, params_path: &str) -> Halo2Prover<Fr, W, WG>;

    /// Create a Halo2 test prover. ⚠️ Not for production use! ⚠️
    /// This prover uses a dummy RNG that outputs fixed values.
    ///
    /// ### Returns
    /// * a test Halo2 prover
    fn create_test_prover(&mut self) -> Halo2Prover<Fr, W, WG>;
}

impl<W, WG: Halo2WitnessGenerator<Fr, W>, T: Halo2Compilable<W, WG>> Halo2Provable<W, WG> for T {
    fn create_halo2_prover(&mut self, params_path: &str) -> Halo2Prover<Fr, W, WG> {
        let (circuit, compiled, k) = self.halo2_compile();
        let mut params_fs = File::open(params_path).expect("couldn't load params");
        let mut params = ParamsKZG::<Bn256>::read(&mut params_fs).expect("Failed to read params");
        if params.k() < k {
            panic!(
                "The provided trusted setup size {} ({params_path}) does not satisfy the circuit size {k}",
                params.k(),
            );
        }
        if params.k() > k {
            params.downsize(k);
        }
        Halo2Prover::new(create_setup(compiled, params), circuit)
    }

    fn create_test_prover(&mut self) -> Halo2Prover<Fr, W, WG> {
        let (circuit, compiled, k) = self.halo2_compile();

        let params = ParamsKZG::<Bn256>::setup::<BlockRng<DummyRng>>(k, BlockRng::new(DummyRng {}));

        Halo2Prover::new(create_setup(compiled, params), circuit)
    }
}

trait Halo2Compilable<W, WG: Halo2WitnessGenerator<Fr, W>> {
    /// Implementation-specific circuit compilation
    fn halo2_compile(&mut self) -> (WG, CompiledCircuit<Fr>, u32);
}

impl<TG: TraceGenerator<Fr> + Clone + Default> Halo2Compilable<Assignments<Fr>, ChiquitoHalo2<Fr>>
    for PlonkishCompilationResult<Fr, TG>
{
    fn halo2_compile(&mut self) -> (ChiquitoHalo2<Fr>, CompiledCircuit<Fr>, u32) {
        let mut circuit = ChiquitoHalo2::new(self.circuit.clone());
        let (compiled, k) = circuit.compile_middleware(self.circuit.num_rows).unwrap();
        (circuit, compiled, k)
    }
}
impl<MappingArgs> Halo2Compilable<SuperAssignments<Fr>, ChiquitoHalo2SuperCircuit<Fr>>
    for SuperCircuit<Fr, MappingArgs>
{
    fn halo2_compile(&mut self) -> (ChiquitoHalo2SuperCircuit<Fr>, CompiledCircuit<Fr>, u32) {
        let compiled = self
            .get_sub_circuits()
            .iter()
            .map(|c| ChiquitoHalo2::new(c.clone()))
            .collect();

        let mut circuit = ChiquitoHalo2SuperCircuit::new(compiled);

        let tallest_subcircuit_height = circuit
            .sub_circuits
            .iter()
            .map(|c| c.plonkish_ir.num_rows)
            .max()
            .unwrap_or(0);

        let (compiled, k) = circuit
            .compile_middleware(tallest_subcircuit_height)
            .unwrap();
        (circuit, compiled, k)
    }
}

fn create_setup(circuit: CompiledCircuit<Fr>, params: ParamsKZG<Bn256>) -> Setup {
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");

    Setup {
        cs: circuit.cs,
        params,
        vk,
        pk,
    }
}

/// ⚠️ Not for production use! ⚠️
///
/// One-number generator that can be used as a deterministic Rng outputting fixed values.
#[derive(Clone)]
pub struct DummyRng {}

impl BlockRngCore for DummyRng {
    type Item = u32;
    type Results = [u32; 16];

    fn generate(&mut self, results: &mut Self::Results) {
        for elem in results.iter_mut() {
            *elem = 1;
        }
    }
}
