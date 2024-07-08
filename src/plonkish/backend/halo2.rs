use std::{collections::HashMap, hash::Hash, vec};

use halo2_backend::plonk::{
    keygen::{keygen_pk, keygen_vk},
    prover::ProverSingle,
    verifier::verify_proof_single,
    Error as ErrorBack,
};
use halo2_middleware::{
    circuit::{Any as Columns, Cell as CellMid, ColumnMid, CompiledCircuit, Preprocessing},
    permutation::AssemblyMid,
    zal::impls::{H2cEngine, PlonkEngineConfig},
};
use halo2_proofs::{
    arithmetic::Field,
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        ff::PrimeField,
    },
    plonk::{
        Advice, Any, Column, ConstraintSystem, ConstraintSystemMid, Error, Expression, FirstPhase,
        Fixed, Instance, ProvingKey, SecondPhase, ThirdPhase, VerifyingKey, VirtualCells,
    },
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
use rand_chacha::rand_core::block::{BlockRng, BlockRngCore};

use crate::{
    field::Field as ChiquitoField,
    plonkish::{
        compiler::PlonkishCompilationResult,
        ir::{
            assignments::Assignments,
            sc::SuperCircuit,
            Circuit, Column as cColumn,
            ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
            PolyExpr,
        },
    },
    poly::ToField,
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

#[allow(non_snake_case)]
pub fn chiquito2Halo2<F: PrimeField + From<u64> + Hash>(circuit: Circuit<F>) -> ChiquitoHalo2<F> {
    ChiquitoHalo2::new(circuit)
}

fn compile_middleware<F: PrimeField + From<u64> + Hash, C: Halo2Configurable<F>>(
    k: u32,
    circuit: &mut C,
) -> Result<CompiledCircuit<F>, Error> {
    let (cs, preprocessing) = circuit.configure(k)?;

    Ok(CompiledCircuit {
        cs: cs.clone().into(),
        preprocessing,
    })
}

#[allow(non_snake_case)]
pub fn chiquitoSuperCircuit2Halo2<F: PrimeField + From<u64> + Hash, MappingArgs>(
    super_circuit: &SuperCircuit<F, MappingArgs>,
) -> Vec<ChiquitoHalo2<F>> {
    super_circuit
        .get_sub_circuits()
        .iter()
        .map(|c| chiquito2Halo2((*c).clone()))
        .collect()
}

#[derive(Clone, Debug, Default)]
pub struct ChiquitoHalo2<F: PrimeField + From<u64>> {
    pub debug: bool,

    pub circuit: Circuit<F>,

    advice_columns: HashMap<UUID, Column<Advice>>,
    fixed_columns: HashMap<UUID, Column<Fixed>>,
    instance_column: Option<Column<Instance>>,

    pub ir_id: UUID,
}

trait Halo2Configurable<F: Field> {
    fn configure(&mut self, k: u32) -> Result<(ConstraintSystem<F>, Preprocessing<F>), Error> {
        let mut cs = self.configure_cs();
        let n = 2usize.pow(k);

        if n < cs.minimum_rows() {
            return Err(Error::Backend(ErrorBack::NotEnoughRowsAvailable {
                current_k: k,
            }));
        }

        let preprocessing = self.preprocessing(&mut cs, n);

        Ok((cs.clone(), preprocessing))
    }

    fn configure_cs(&mut self) -> ConstraintSystem<F>;
    fn preprocessing(&self, cs: &mut ConstraintSystem<F>, n: usize) -> Preprocessing<F>;
}

impl<F: PrimeField + Hash> Halo2Configurable<F> for ChiquitoHalo2<F> {
    fn preprocessing(&self, cs: &mut ConstraintSystem<F>, n: usize) -> Preprocessing<F> {
        let fixed_count = self.circuit.fixed_assignments.0.len();
        let mut fixed = vec![vec![F::default(); n]; fixed_count];

        for (column, values) in self.circuit.fixed_assignments.iter() {
            let column = self.convert_fixed_column(column);

            for (offset, value) in values.iter().enumerate() {
                fixed[column.index][offset] = *value;
            }
        }

        let mut copies = vec![];
        self.collect_permutations(cs, &mut copies);

        Preprocessing {
            permutation: AssemblyMid { copies },
            fixed,
        }
    }

    fn configure_cs(&mut self) -> ConstraintSystem<F> {
        let mut cs: ConstraintSystem<F> = ConstraintSystem::default();

        self.configure_columns_sub_circuit(&mut cs);

        self.configure_sub_circuit(&mut cs);

        cs
    }
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2<F> {
    pub fn new(circuit: Circuit<F>) -> ChiquitoHalo2<F> {
        let ir_id = circuit.id;
        ChiquitoHalo2 {
            debug: true,
            circuit,
            advice_columns: Default::default(),
            fixed_columns: Default::default(),
            instance_column: Default::default(),
            ir_id,
        }
    }

    fn configure_columns_sub_circuit(&mut self, meta: &mut ConstraintSystem<F>) {
        let mut advice_columns = HashMap::<UUID, Column<Advice>>::new();
        let mut fixed_columns = HashMap::<UUID, Column<Fixed>>::new();

        for column in self.circuit.columns.iter() {
            match column.ctype {
                cAdvice => {
                    let halo2_column = to_halo2_advice(meta, column);
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                cFixed => {
                    let halo2_column = meta.fixed_column();
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Advice => {
                    let halo2_column = column
                        .halo2_advice
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Fixed => {
                    let halo2_column = column
                        .halo2_fixed
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
            }
        }

        self.advice_columns = advice_columns;
        self.fixed_columns = fixed_columns;
    }

    fn configure_sub_circuit(&mut self, meta: &mut ConstraintSystem<F>) {
        if !self.circuit.exposed.is_empty() {
            self.instance_column = Some(meta.instance_column());
        }

        if !self.circuit.polys.is_empty() {
            meta.create_gate("main", |meta| {
                let mut constraints: Vec<(&'static str, Expression<F>)> = Vec::new();

                for poly in self.circuit.polys.iter() {
                    let converted = self.convert_poly(meta, &poly.expr);
                    let annotation = Box::leak(
                        format!("{} => {:?}", poly.annotation, converted).into_boxed_str(),
                    );
                    constraints.push((annotation, converted));
                }

                constraints
            });
        }

        for lookup in self.circuit.lookups.iter() {
            let annotation: &'static str = Box::leak(lookup.annotation.clone().into_boxed_str());
            meta.lookup_any(annotation, |meta| {
                let mut exprs = Vec::new();
                for (src, dest) in lookup.exprs.iter() {
                    exprs.push((self.convert_poly(meta, src), self.convert_poly(meta, dest)))
                }

                exprs
            });
        }
    }

    fn convert_poly(&self, meta: &mut VirtualCells<'_, F>, src: &PolyExpr<F>) -> Expression<F> {
        match src {
            PolyExpr::Const(c, _) => Expression::Constant(*c),
            PolyExpr::Sum(es, _) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.convert_poly(meta, e))
            }
            PolyExpr::Mul(es, _) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.convert_poly(meta, e))
            }
            PolyExpr::Neg(e, _) => -self.convert_poly(meta, e),
            PolyExpr::Pow(e, n, _) => {
                if *n == 0 {
                    Expression::Constant(1.field())
                } else {
                    let e = self.convert_poly(meta, e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            PolyExpr::Halo2Expr(e, _) => e.clone(),
            PolyExpr::Query((column, rotation, _), _) => {
                self.convert_query(meta, column, *rotation)
            }
            PolyExpr::MI(_, _) => panic!("mi elimination not done"),
        }
    }

    fn convert_query(
        &self,
        meta: &mut VirtualCells<'_, F>,
        column: &cColumn,
        rotation: i32,
    ) -> Expression<F> {
        match column.ctype {
            cAdvice | Halo2Advice => {
                let c = self
                    .advice_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_advice(*c, Rotation(rotation))
            }
            cFixed | Halo2Fixed => {
                let c = self
                    .fixed_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_fixed(*c, Rotation(rotation))
            }
        }
    }

    fn convert_advice_column(&self, column: &cColumn) -> Column<Advice> {
        match column.ctype {
            cAdvice | Halo2Advice => *self
                .advice_columns
                .get(&column.uuid())
                .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            _ => panic!("wrong column type"),
        }
    }

    fn convert_fixed_column(&self, column: &cColumn) -> Column<Fixed> {
        match column.ctype {
            cFixed | Halo2Fixed => *self
                .fixed_columns
                .get(&column.uuid())
                .unwrap_or_else(|| panic!("column not found {}", column.annotation)),
            _ => panic!("wrong column type"),
        }
    }

    fn collect_permutations(
        &self,
        cs: &mut ConstraintSystem<F>,
        copies: &mut Vec<(CellMid, CellMid)>,
    ) {
        self.circuit
            .exposed
            .iter()
            .enumerate()
            .for_each(|(row, (column, offset))| {
                let col_type: Columns = match column.ctype {
                    cAdvice | Halo2Advice => Columns::Advice,
                    cFixed | Halo2Fixed => Columns::Fixed,
                };

                let index = if col_type == Columns::Advice {
                    let column = self.convert_advice_column(column);
                    cs.enable_equality(column);
                    column.index
                } else {
                    let column = self.convert_fixed_column(column);
                    cs.enable_equality(column);
                    column.index
                };

                let column_mid = ColumnMid::new(col_type, index);

                let instance_column = ColumnMid::new(Columns::Instance, 0);
                cs.enable_equality(instance_column);
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
}

fn to_halo2_advice<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    column: &cColumn,
) -> Column<Advice> {
    match column.phase {
        0 => meta.advice_column_in(FirstPhase),
        1 => meta.advice_column_in(SecondPhase),
        2 => meta.advice_column_in(ThirdPhase),
        _ => panic!("jarll wrong phase"),
    }
}

#[derive(Clone, Debug, Default)]
pub struct ChiquitoHalo2SuperCircuit<F: PrimeField + From<u64>> {
    sub_circuits: Vec<ChiquitoHalo2<F>>,
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2SuperCircuit<F> {
    pub fn new(sub_circuits: Vec<ChiquitoHalo2<F>>) -> Self {
        Self { sub_circuits }
    }
}

impl<F: PrimeField + Hash> Halo2Configurable<F> for ChiquitoHalo2SuperCircuit<F> {
    fn configure_cs(&mut self) -> ConstraintSystem<F> {
        let mut cs = ConstraintSystem::default();

        self.sub_circuits
            .iter_mut()
            .for_each(|c| c.configure_columns_sub_circuit(&mut cs));

        let advice_columns: HashMap<UUID, Column<Advice>> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.advice_columns.clone());
                    acc
                });
        let fixed_columns: HashMap<UUID, Column<Fixed>> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.fixed_columns.clone());
                    acc
                });

        self.sub_circuits.iter_mut().for_each(|sub_circuit| {
            sub_circuit.advice_columns = advice_columns.clone();
            sub_circuit.fixed_columns = fixed_columns.clone();
            sub_circuit.configure_sub_circuit(&mut cs)
        });

        cs
    }

    fn preprocessing(&self, cs: &mut ConstraintSystem<F>, n: usize) -> Preprocessing<F> {
        let fixed_columns: HashMap<UUID, Column<Fixed>> =
            self.sub_circuits
                .iter()
                .fold(HashMap::default(), |mut acc, s| {
                    acc.extend(s.fixed_columns.clone());
                    acc
                });

        let fixed_count = fixed_columns.len();
        let mut fixed = vec![vec![F::default(); n]; fixed_count];

        let mut copies = vec![];
        for subcircuit in self.sub_circuits.iter() {
            for (column, values) in subcircuit.circuit.fixed_assignments.iter() {
                let column = fixed_columns.get(&column.uuid()).unwrap();

                for (offset, value) in values.iter().enumerate() {
                    fixed[column.index][offset] = *value;
                }
            }
            subcircuit.collect_permutations(cs, &mut copies);
        }

        Preprocessing {
            permutation: AssemblyMid { copies },
            fixed,
        }
    }
}

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

pub struct Setup {
    pub cs: ConstraintSystemMid<Fr>,
    pub params: ParamsKZG<Bn256>,
    pub vk: VerifyingKey<G1Affine>,
    pub pk: ProvingKey<G1Affine>,
}

pub struct SingleCircuitProver<F: PrimeField> {
    pub setup: Setup,
    circuit: ChiquitoHalo2<F>,
}
impl SingleCircuitProver<Fr> {
    pub fn generate_proof(
        &self,
        mut rng: BlockRng<DummyRng>,
        witness: &Assignments<Fr>,
    ) -> (Vec<u8>, Vec<Vec<Fr>>) {
        let mut instance = Vec::new();

        if !self.circuit.circuit.exposed.is_empty() {
            let instance_values = self.circuit.circuit.instance(witness);
            instance.push(instance_values);
        }

        // Proving
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        let mut prover = create_prover(&self.setup, &instance, &mut rng, &mut transcript);

        for phase in 0..self.setup.cs.phases() {
            let mut assigned_witness =
                vec![
                    Some(vec![Fr::default(); self.setup.params.n() as usize]);
                    self.setup.cs.num_advice_columns
                ];

            assign_witness(&self.circuit, witness, &mut assigned_witness);

            // TODO ignoring the challenges produced by the phase, but can they be useful later?
            let _ = prover.commit_phase(phase as u8, assigned_witness).unwrap();
        }
        prover.create_proof().unwrap();
        let proof = transcript.finalize();

        (proof, instance)
    }
}

#[allow(clippy::type_complexity)]
fn create_prover<'a>(
    setup: &'a Setup,
    instance: &[Vec<Fr>],
    rng: &'a mut BlockRng<DummyRng>,
    transcript: &'a mut Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
) -> ProverSingle<
    'a,
    'a,
    KZGCommitmentScheme<Bn256>,
    ProverSHPLONK<'a, Bn256>,
    Challenge255<G1Affine>,
    &'a mut BlockRng<DummyRng>,
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
             rng,
            transcript,
        )
        .unwrap()
}

fn assign_witness(
    circuit: &ChiquitoHalo2<Fr>,
    witness: &Assignments<Fr>,
    assigned_witness: &mut [Option<Vec<Fr>>],
) {
    for (column, values) in witness.iter() {
        let circuit_column = circuit.advice_columns.get(&column.uuid()).unwrap();
        let halo2_column = Column::<Any>::from(*circuit_column);
        for (offset, value) in values.iter().enumerate() {
            assigned_witness[halo2_column.index].as_mut().unwrap()[offset] = *value;
        }
    }
}

pub struct SuperCircuitProver<F: PrimeField> {
    pub setup: Setup,
    circuit: ChiquitoHalo2SuperCircuit<F>,
}
impl SuperCircuitProver<Fr> {
    pub fn generate_proof(
        &self,
        mut rng: BlockRng<DummyRng>,
        witnesses: HashMap<UUID, Assignments<Fr>>,
    ) -> (Vec<u8>, Vec<Vec<Fr>>) {
        let mut instance = Vec::new();

        for circuit in self.circuit.sub_circuits.iter() {
            if !circuit.circuit.exposed.is_empty() {
                let instance_values = circuit.circuit.instance(
                    witnesses
                        .get(&circuit.ir_id)
                        .expect("No matching witness found for given UUID."),
                );
                instance.push(instance_values);
            }
        }

        // Proving
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        let mut prover = create_prover(&self.setup, &instance, &mut rng, &mut transcript);

        for phase in 0..self.setup.cs.phases() {
            let mut assigned_witness =
                vec![
                    Some(vec![Fr::default(); self.setup.params.n() as usize]);
                    self.setup.cs.num_advice_columns
                ];

            for circuit in self.circuit.sub_circuits.iter() {
                if let Some(assignments) = witnesses.get(&circuit.ir_id) {
                    assign_witness(circuit, assignments, &mut assigned_witness);
                }
            }

            // TODO ignoring the challenges produced by the phase, but can they be useful later?
            let _ = prover.commit_phase(phase as u8, assigned_witness).unwrap();
        }
        prover.create_proof().unwrap();
        let proof = transcript.finalize();

        (proof, instance)
    }
}

pub trait PlonkishHalo2<F: PrimeField, P> {
    fn create_halo2_prover(&mut self, k: u32, rng: BlockRng<DummyRng>) -> P;
}

impl<TG: TraceGenerator<Fr> + Default> PlonkishHalo2<Fr, SingleCircuitProver<Fr>>
    for PlonkishCompilationResult<Fr, TG>
{
    fn create_halo2_prover(&mut self, k: u32, rng: BlockRng<DummyRng>) -> SingleCircuitProver<Fr> {
        let mut circuit = ChiquitoHalo2::new(self.circuit.clone());
        let compiled = compile_middleware(k, &mut circuit).unwrap();
        let setup = create_setup(k, rng, compiled);
        SingleCircuitProver { setup, circuit }
    }
}

impl PlonkishHalo2<Fr, SuperCircuitProver<Fr>> for ChiquitoHalo2SuperCircuit<Fr> {
    fn create_halo2_prover(&mut self, k: u32, rng: BlockRng<DummyRng>) -> SuperCircuitProver<Fr> {
        let compiled = compile_middleware(k, self).unwrap();
        let setup = create_setup(k, rng, compiled);
        SuperCircuitProver {
            circuit: self.clone(),
            setup,
        }
    }
}

fn create_setup(k: u32, rng: BlockRng<DummyRng>, circuit: CompiledCircuit<Fr>) -> Setup {
    let params = ParamsKZG::<Bn256>::setup::<BlockRng<DummyRng>>(k, rng);
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
