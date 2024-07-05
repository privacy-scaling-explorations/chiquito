use std::{collections::HashMap, hash::Hash, time::Instant, vec};

use halo2_backend::plonk::{
    keygen::{keygen_pk, keygen_vk},
    prover::ProverSingle,
    verifier::verify_proof_single,
    Error as ErrorBack,
};
use halo2_middleware::{
    circuit::{Any as Columns, Cell as CellMid, ColumnMid, CompiledCircuit, Preprocessing},
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

fn compile_halo2_middleware<F: PrimeField + From<u64> + Hash, C: Halo2Configurable<F>>(
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
            permutation: halo2_middleware::permutation::AssemblyMid { copies },
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

#[derive(Debug, Default)]
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
            permutation: halo2_middleware::permutation::AssemblyMid { copies },
            fixed,
        }
    }
}

pub fn halo2_verify(
    proof: Vec<u8>,
    params: ParamsKZG<Bn256>,
    vk: VerifyingKey<G1Affine>,
    instance: Vec<Vec<Fr>>,
) -> Result<(), ErrorBack> {
    // Verify
    let start = Instant::now();
    println!("Verifying...");
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&verifier_params);

    let result = verify_proof_single::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, _, _, _>(
        &verifier_params,
        &vk,
        strategy,
        instance,
        &mut verifier_transcript,
    );
    println!("Verify: {:?}", start.elapsed());
    result
}

pub struct Halo2Setup {
    cs: ConstraintSystemMid<Fr>,
    pub params: ParamsKZG<Bn256>,
    pub vk: VerifyingKey<G1Affine>,
    pk: ProvingKey<G1Affine>,
    pub circuits: Vec<ChiquitoHalo2<Fr>>,
}

impl Halo2Setup {
    pub fn new(
        cs: ConstraintSystemMid<Fr>,
        params: ParamsKZG<Bn256>,
        vk: VerifyingKey<G1Affine>,
        pk: ProvingKey<G1Affine>,
        circuits: Vec<ChiquitoHalo2<Fr>>,
    ) -> Self {
        Self {
            cs,
            params,
            vk,
            pk,
            circuits,
        }
    }

    pub fn generate_proof(
        &self,
        mut rng: BlockRng<DummyRng>,
        witnesses: HashMap<UUID, Assignments<Fr>>,
    ) -> (Vec<u8>, Vec<Vec<Fr>>) {
        let mut instance = Vec::new();

        for circuit in self.circuits.iter() {
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
        println!("Proving...");
        let start = Instant::now();
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        let engine = PlonkEngineConfig::new()
            .set_curve::<G1Affine>()
            .set_msm(H2cEngine::new())
            .build();

        let mut prover = ProverSingle::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            _,
            _,
            _,
            _,
        >::new_with_engine(
            engine,
            &self.params,
            &self.pk,
            instance.clone(),
            &mut rng,
            &mut transcript,
        )
        .unwrap();

        for phase in 0..self.cs.phases() {
            println!("Phase {phase}");

            let mut assigned_witness = vec![
                Some(vec![Fr::default(); self.params.n() as usize]);
                self.cs.num_advice_columns
            ];

            for circuit in self.circuits.iter() {
                if let Some(assignments) = witnesses.get(&circuit.ir_id) {
                    for (column, values) in assignments.iter() {
                        let circuit_column = circuit.advice_columns.get(&column.uuid()).unwrap();
                        let halo2_column = Column::<Any>::from(*circuit_column);
                        for (offset, value) in values.iter().enumerate() {
                            assigned_witness[halo2_column.index].as_mut().unwrap()[offset] = *value;
                        }
                    }
                }
            }

            // TODO ignoring the challenges produced by the phase, but can they be useful later?
            let _ = prover.commit_phase(phase as u8, assigned_witness).unwrap();
            println!("Phase {phase} completed");
        }
        println!("Creating proof...");
        prover.create_proof().unwrap();
        let proof = transcript.finalize();
        println!("Prove: {:?}", start.elapsed());

        (proof, instance)
    }
}

pub trait PlonkishHalo2<F: PrimeField> {
    fn halo2_setup(&mut self, k: u32, rng: BlockRng<DummyRng>) -> Halo2Setup;
}

impl<TG: TraceGenerator<Fr> + Default> PlonkishHalo2<Fr> for PlonkishCompilationResult<Fr, TG> {
    fn halo2_setup(&mut self, k: u32, rng: BlockRng<DummyRng>) -> Halo2Setup {
        let mut chiquito_halo2 = ChiquitoHalo2::new(self.circuit.clone());
        let compiled = compile_halo2_middleware(k, &mut chiquito_halo2).unwrap();
        // Setup
        let params = ParamsKZG::<Bn256>::setup::<BlockRng<DummyRng>>(k, rng);
        let vk = keygen_vk(&params, &compiled).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk.clone(), &compiled).expect("keygen_pk should not fail");

        Halo2Setup::new(compiled.cs, params, vk, pk, vec![chiquito_halo2])
    }
}

impl PlonkishHalo2<Fr> for ChiquitoHalo2SuperCircuit<Fr> {
    fn halo2_setup(&mut self, k: u32, rng: BlockRng<DummyRng>) -> Halo2Setup {
        let compiled = compile_halo2_middleware(k, self).unwrap();
        // Setup
        let params = ParamsKZG::<Bn256>::setup::<BlockRng<DummyRng>>(k, rng);
        let vk = keygen_vk(&params, &compiled).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk.clone(), &compiled).expect("keygen_pk should not fail");

        Halo2Setup::new(compiled.cs, params, vk, pk, self.sub_circuits.clone())
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
