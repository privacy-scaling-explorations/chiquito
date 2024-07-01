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
    circuit::{Cell, Layouter, Region, RegionIndex, SimpleFloorPlanner, Value},
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        ff::PrimeField,
    },
    plonk::{
        Advice, Any, Circuit as h2Circuit, Column, ConstraintSystem, ConstraintSystemMid, Error,
        ErrorFront, Expression, FirstPhase, Fixed, Instance, ProvingKey, SecondPhase, ThirdPhase,
        VerifyingKey, VirtualCells,
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
    plonkish::ir::{
        assignments::Assignments,
        sc::{SuperAssignments, SuperCircuit},
        Circuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr,
    },
    poly::ToField,
    util::UUID,
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

pub fn compile_halo2_middleware<F: PrimeField + From<u64> + Hash>(
    k: u32,
    circuit: &mut ChiquitoHalo2<F>,
) -> Result<CompiledCircuit<F>, Error> {
    let n = 2usize.pow(k);

    let mut cs = ConstraintSystem::default();

    if n < cs.minimum_rows() {
        return Err(Error::Frontend(ErrorFront::NotEnoughRowsAvailable {
            current_k: k,
        }));
    }

    circuit.configure(&mut cs);

    let fixed_count = circuit.circuit.fixed_assignments.0.len();
    let mut fixed = vec![vec![F::default(); n]; fixed_count];

    for (column, values) in circuit.circuit.fixed_assignments.iter() {
        let column = circuit.convert_fixed_column(column);

        for (offset, value) in values.iter().enumerate() {
            fixed[column.index][offset] = *value;
        }
    }

    let mut copies = vec![];
    circuit
        .circuit
        .exposed
        .iter()
        .enumerate()
        .for_each(|(row, (column, offset))| {
            let col_type: Columns = match column.ctype {
                cAdvice | Halo2Advice => Columns::Advice,
                cFixed | Halo2Fixed => Columns::Fixed,
            };

            let index = if col_type == Columns::Advice {
                circuit.convert_advice_column(column).index
            } else {
                circuit.convert_fixed_column(column).index
            };

            let column_mid = ColumnMid::new(col_type, index);

            copies.push((
                CellMid {
                    column: column_mid,
                    row: *offset as usize,
                },
                CellMid {
                    column: ColumnMid::new(Columns::Instance, 0),
                    row,
                },
            ));
        });

    let preprocessing = Preprocessing {
        permutation: halo2_middleware::permutation::AssemblyMid { copies: vec![] },
        fixed,
    };

    Ok(CompiledCircuit {
        cs: cs.clone().into(),
        preprocessing,
    })
}

pub fn compile_super_circuit_halo2_middleware<F: PrimeField + From<u64> + Hash>(
    k: u32,
    circuit: &mut ChiquitoHalo2SuperCircuit<F>,
) -> Result<CompiledCircuit<F>, Error> {
    let n = 2usize.pow(k);

    let mut cs = ConstraintSystem::default();

    if n < cs.minimum_rows() {
        return Err(Error::Frontend(ErrorFront::NotEnoughRowsAvailable {
            current_k: k,
        }));
    }

    circuit.sub_circuits =
        ChiquitoHalo2SuperCircuit::configure_with_params(&mut cs, circuit.sub_circuits.clone());

    let fixed_columns: HashMap<UUID, Column<Fixed>> =
        circuit
            .sub_circuits
            .iter()
            .fold(HashMap::default(), |mut acc, s| {
                acc.extend(s.fixed_columns.clone());
                acc
            });

    let fixed_count = fixed_columns.len();
    let mut fixed = vec![vec![F::default(); n]; fixed_count];

    for subcircuit in circuit.sub_circuits.iter() {
        for (column, values) in subcircuit.circuit.fixed_assignments.iter() {
            let column = fixed_columns.get(&column.uuid()).unwrap();

            for (offset, value) in values.iter().enumerate() {
                fixed[column.index][offset] = *value;
            }
        }
    }

    let preprocessing = Preprocessing {
        permutation: halo2_middleware::permutation::AssemblyMid { copies: vec![] },
        fixed,
    };

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
    pub fixed_columns: HashMap<UUID, Column<Fixed>>,
    instance_column: Option<Column<Instance>>,

    ir_id: UUID,
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

    pub fn instance(&self, witness: &Assignments<F>) -> Vec<F> {
        self.circuit.instance(witness)
    }

    pub fn configure(&mut self, meta: &mut ConstraintSystem<F>) {
        self.configure_columns_sub_circuit(meta);

        self.configure_sub_circuit(meta);
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

    pub fn configure_sub_circuit(&mut self, meta: &mut ConstraintSystem<F>) {
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

    pub fn synthesize(&self, layouter: &mut impl Layouter<F>, witness: Option<&Assignments<F>>) {
        let _ = layouter.assign_region(
            || "circuit",
            |mut region| {
                self.annotate_circuit(&mut region);

                self.assign_fixed(&mut region, &self.circuit.fixed_assignments)?;

                if let Some(witness) = &witness {
                    self.assign_advice(&mut region, witness)?;
                }

                Ok(())
            },
        );

        for (index, (column, rotation)) in self.circuit.exposed.iter().enumerate() {
            println!("exposed {}", index);
            let halo2_column =
                Column::<Any>::from(*self.advice_columns.get(&column.uuid()).unwrap());
            let cell = new_cell(
                halo2_column,
                // For single row cell manager, forward signal rotation is always zero.
                // For max width cell manager, rotation can be non-zero.
                // Offset is absolute row index calculated in `compile_exposed`.
                *rotation as usize,
            );
            let _ = layouter.constrain_instance(cell, self.instance_column.unwrap(), index);
        }
    }

    fn assign_advice(
        &self,
        region: &mut Region<F>,
        witness: &Assignments<F>,
    ) -> Result<(), ErrorFront> {
        for (column, assignments) in witness.iter() {
            let column = self.convert_advice_column(column);

            for (offset, value) in assignments.iter().enumerate() {
                region.assign_advice(|| "", column, offset, || Value::known(*value))?;
            }
        }

        Ok(())
    }

    fn assign_fixed(
        &self,
        region: &mut Region<F>,
        fixed: &Assignments<F>,
    ) -> Result<(), ErrorFront> {
        for (column, values) in fixed.iter() {
            let column = self.convert_fixed_column(column);

            for (offset, value) in values.iter().enumerate() {
                region.assign_fixed(|| "", column, offset, || Value::known(*value))?;
            }
        }

        Ok(())
    }

    fn annotate_circuit(&self, region: &mut Region<F>) {
        for column in self.circuit.columns.iter() {
            match column.ctype {
                cAdvice | Halo2Advice => {
                    let halo2_column = self
                        .advice_columns
                        .get(&column.uuid())
                        .expect("advice column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column);
                }
                cFixed | Halo2Fixed => {
                    let halo2_column = self
                        .fixed_columns
                        .get(&column.uuid())
                        .expect("fixed column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column);
                }
            }
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
}

#[allow(dead_code)]
// From Plaf Halo2 backend.
// _Cell is a helper struct used for constructing Halo2 Cell.
struct _Cell {
    region_index: RegionIndex,
    row_offset: usize,
    column: Column<Any>,
}
// From Plaf Halo2 backend.
fn new_cell(column: Column<Any>, offset: usize) -> Cell {
    let cell = _Cell {
        region_index: RegionIndex::from(0),
        row_offset: offset,
        column,
    };
    // NOTE: We use unsafe here to construct a Cell, which doesn't have a public constructor.  This
    // helps us set the copy constraints easily (without having to store all assigned cells
    // previously)
    unsafe { std::mem::transmute::<_Cell, Cell>(cell) }
}

pub fn to_halo2_advice<F: PrimeField>(
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

#[derive(Clone, Default, Debug)]
pub struct ChiquitoHalo2Circuit<F: PrimeField + From<u64>> {
    compiled: ChiquitoHalo2<F>,
    witness: Option<Assignments<F>>,
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2Circuit<F> {
    pub fn new(compiled: ChiquitoHalo2<F>, witness: Option<Assignments<F>>) -> Self {
        Self { compiled, witness }
    }

    pub fn instance(&self) -> Vec<Vec<F>> {
        if !self.compiled.circuit.exposed.is_empty() {
            if let Some(witness) = &self.witness {
                return vec![self.compiled.circuit.instance(witness)];
            }
        }
        Vec::new()
    }
}

impl<F: PrimeField + From<u64> + Hash> h2Circuit<F> for ChiquitoHalo2Circuit<F> {
    type Config = ChiquitoHalo2<F>;

    type FloorPlanner = SimpleFloorPlanner;

    type Params = ChiquitoHalo2<F>;

    fn without_witnesses(&self) -> Self {
        Self {
            compiled: self.compiled.clone(),
            witness: self.witness.clone().map(|mut w| {
                w.clear();
                w
            }),
        }
    }

    fn params(&self) -> Self::Params {
        self.compiled.clone()
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        mut compiled: Self::Params,
    ) -> Self::Config {
        compiled.configure(meta);

        compiled
    }

    fn synthesize(
        &self,
        compiled: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        compiled.synthesize(&mut layouter, self.witness.as_ref());

        Ok(())
    }

    fn configure(_: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!()
    }
}

#[derive(Debug, Default)]
pub struct ChiquitoHalo2SuperCircuit<F: PrimeField + From<u64>> {
    pub sub_circuits: Vec<ChiquitoHalo2<F>>,
    // TODO witness is only necessary to get the instance values, can it be removed later?
    witness: SuperAssignments<F>,
}

impl<F: PrimeField + From<u64> + Hash> ChiquitoHalo2SuperCircuit<F> {
    pub fn new(sub_circuits: Vec<ChiquitoHalo2<F>>, witness: SuperAssignments<F>) -> Self {
        Self {
            sub_circuits,
            witness,
        }
    }

    pub fn instance(&self) -> Vec<Vec<F>> {
        let mut result = Vec::new();

        for sub_circuit in &self.sub_circuits {
            if !sub_circuit.circuit.exposed.is_empty() {
                let instance_values = sub_circuit.circuit.instance(
                    self.witness
                        .get(&sub_circuit.ir_id)
                        .expect("No matching witness found for given UUID."),
                );
                result.push(instance_values);
            }
        }

        result
    }
}

impl<F: PrimeField + From<u64> + Hash> h2Circuit<F> for ChiquitoHalo2SuperCircuit<F> {
    type Config = Vec<ChiquitoHalo2<F>>;

    type FloorPlanner = SimpleFloorPlanner;

    type Params = Vec<ChiquitoHalo2<F>>;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        self.sub_circuits.clone()
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        mut sub_circuits: Self::Params,
    ) -> Self::Config {
        sub_circuits
            .iter_mut()
            .for_each(|c| c.configure_columns_sub_circuit(meta));

        let advice_columns: HashMap<UUID, Column<Advice>> =
            sub_circuits.iter().fold(HashMap::default(), |mut acc, s| {
                acc.extend(s.advice_columns.clone());
                acc
            });
        let fixed_columns: HashMap<UUID, Column<Fixed>> =
            sub_circuits.iter().fold(HashMap::default(), |mut acc, s| {
                acc.extend(s.fixed_columns.clone());
                acc
            });

        sub_circuits.iter_mut().for_each(|sub_circuit| {
            sub_circuit.advice_columns = advice_columns.clone();
            sub_circuit.fixed_columns = fixed_columns.clone();
            sub_circuit.configure_sub_circuit(meta)
        });

        sub_circuits
    }

    fn synthesize(
        &self,
        sub_circuits: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        for sub_circuit in sub_circuits {
            sub_circuit.synthesize(&mut layouter, self.witness.get(&sub_circuit.ir_id))
        }

        Ok(())
    }

    fn configure(_: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!()
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

pub fn halo2_prove(
    params: &ParamsKZG<Bn256>,
    pk: ProvingKey<G1Affine>,
    mut rng: BlockRng<OneNg>,
    cs: ConstraintSystemMid<Fr>,
    witnesses: Vec<&Assignments<Fr>>,
    circuits: Vec<ChiquitoHalo2<Fr>>,
    instance: Vec<Vec<Fr>>,
) -> Vec<u8> {
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
            params,
            &pk,
            instance.clone(),
            &mut rng,
            &mut transcript,
        )
        .unwrap();

    for phase in 0..cs.phases() {
        println!("phase {phase}");

        let mut assigned_witness =
            vec![Some(vec![Fr::default(); params.n() as usize]); cs.num_advice_columns];

        // TODO as super_circuit.get_mapping().generate() creates a mapping of "compilation unit" ID
        // to a witness, currently it is impossible to get a witness by the circuit id, hence we are
        // iterating over all witnesses and checking if the circuit has a column in
        // question.
        for witness in witnesses.iter() {
            for (column, assignments) in witness.iter() {
                for circuit in circuits.iter() {
                    if let Some(circuit_column) = circuit.advice_columns.get(&column.uuid()) {
                        let halo2_column = Column::<Any>::from(*circuit_column);
                        for (offset, value) in assignments.iter().enumerate() {
                            assigned_witness[halo2_column.index].as_mut().unwrap()[offset] = *value;
                        }
                    }
                }
            }
        }

        // TODO ignoring the challenges produced by the phase, but can they be useful later?
        let _ = prover.commit_phase(phase as u8, assigned_witness).unwrap();
        println!("phase {phase} completed");
    }
    prover.create_proof().unwrap();
    let proof = transcript.finalize();
    println!("Prove: {:?}", start.elapsed());

    proof
}

#[allow(clippy::type_complexity)]
pub fn get_halo2_settings(
    k: u32,
    circuit: Circuit<Fr>,
    rng: BlockRng<OneNg>,
) -> (
    ConstraintSystemMid<Fr>,
    ParamsKZG<Bn256>,
    VerifyingKey<G1Affine>,
    ProvingKey<G1Affine>,
    ChiquitoHalo2<Fr>,
) {
    let mut chiquito_halo2 = ChiquitoHalo2::new(circuit);

    let compiled = compile_halo2_middleware::<Fr>(k, &mut chiquito_halo2).unwrap();
    // Setup
    let params = ParamsKZG::<Bn256>::setup::<BlockRng<OneNg>>(k, rng);
    let vk = keygen_vk(&params, &compiled).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &compiled).expect("keygen_pk should not fail");

    (compiled.cs, params, vk, pk, chiquito_halo2)
}

pub fn get_super_circuit_halo2(
    k: u32,
    circuit: &mut ChiquitoHalo2SuperCircuit<Fr>,
    rng: BlockRng<OneNg>,
) -> (
    ConstraintSystemMid<Fr>,
    ParamsKZG<Bn256>,
    halo2_proofs::plonk::VerifyingKey<G1Affine>,
    halo2_proofs::plonk::ProvingKey<G1Affine>,
) {
    let compiled = compile_super_circuit_halo2_middleware::<Fr>(k, circuit).unwrap();
    // Setup
    let params = ParamsKZG::<Bn256>::setup::<BlockRng<OneNg>>(k, rng);
    let vk = keygen_vk(&params, &compiled).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &compiled).expect("keygen_pk should not fail");

    (compiled.cs, params, vk, pk)
}

// One number generator, that can be used as a deterministic Rng, outputting fixed values.
pub struct OneNg {}

impl BlockRngCore for OneNg {
    type Item = u32;
    type Results = [u32; 16];

    fn generate(&mut self, results: &mut Self::Results) {
        for elem in results.iter_mut() {
            *elem = 1;
        }
    }
}
