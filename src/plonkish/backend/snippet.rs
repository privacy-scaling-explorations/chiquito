#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlonkishCircuitInfo<F> {
    /// 2^k is the size of the circuit
    pub k: usize,
    /// Number of instnace value in each instance polynomial.
    pub num_instances: Vec<usize>,
    /// Preprocessed polynomials, which has index starts with offset
    /// `num_instances.len()`.
    pub preprocess_polys: Vec<Vec<F>>,
    /// Number of witness polynoimal in each phase.
    /// Witness polynomial index starts with offset `num_instances.len()` +
    /// `preprocess_polys.len()`.
    pub num_witness_polys: Vec<usize>,
    /// Number of challenge in each phase.
    pub num_challenges: Vec<usize>,
    /// Constraints.
    pub constraints: Vec<Expression<F>>,
    /// Each item inside outer vector repesents an independent vector lookup,
    /// which contains vector of tuples representing the input and table
    /// respectively.
    pub lookups: Vec<Vec<(Expression<F>, Expression<F>)>>,
    /// Each item inside outer vector repesents an closed permutation cycle,
    /// which contains vetor of tuples representing the polynomial index and
    /// row respectively.
    pub permutations: Vec<Vec<(usize, usize)>>,
    /// Maximum degree of constraints
    pub max_degree: Option<usize>,
}

pub trait PlonkishCircuit<F> {
    fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<F>, Error>;

    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<F>, Error>;

    fn instances(&self) -> &[Vec<F>];

    fn synthesize(&self, round: usize, challenges: &[F]) -> Result<Vec<Vec<F>>, Error>;
}

impl<F: Field, C: Circuit<F>> PlonkishCircuit<F> for Halo2Circuit<F, C> {
    fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<F>, crate::Error> {
        let Self {
            k,
            instances,
            cs,
            challenge_idx,
            ..
        } = self;
        let advice_idx = advice_idx(cs);
        let constraints = cs
            .gates()
            .iter()
            .flat_map(|gate| {
                gate.polynomials().iter().map(|expression| {
                    convert_expression(cs, &advice_idx, challenge_idx, expression)
                })
            })
            .collect();
        let lookups = cs
            .lookups()
            .iter()
            .map(|lookup| {
                lookup
                    .input_expressions()
                    .iter()
                    .zip(lookup.table_expressions())
                    .map(|(input, table)| {
                        let [input, table] = [input, table].map(|expression| {
                            convert_expression(cs, &advice_idx, challenge_idx, expression)
                        });
                        (input, table)
                    })
                    .collect_vec()
            })
            .collect();

        let num_instances = instances.iter().map(Vec::len).collect_vec();
        let preprocess_polys =
            vec![vec![F::ZERO; 1 << k]; cs.num_selectors() + cs.num_fixed_columns()];
        let column_idx = column_idx(cs);
        let permutations = cs
            .permutation()
            .get_columns()
            .iter()
            .map(|column| {
                let key = (*column.column_type(), column.index());
                vec![(column_idx[&key], 1)]
            })
            .collect_vec();

        Ok(PlonkishCircuitInfo {
            k: *k as usize,
            num_instances,
            preprocess_polys,
            num_witness_polys: num_by_phase(&cs.advice_column_phase()),
            num_challenges: num_by_phase(&cs.challenge_phase()),
            constraints,
            lookups,
            permutations,
            max_degree: Some(cs.degree::<false>()),
        })
    }

    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<F>, crate::Error> {
        let Self {
            k,
            instances,
            cs,
            config,
            circuit,
            constants,
            row_mapping,
            ..
        } = self;
        let mut circuit_info = self.circuit_info_without_preprocess()?;

        let num_instances = instances.iter().map(Vec::len).collect_vec();
        let column_idx = column_idx(cs);
        let permutation_column_idx = cs
            .permutation()
            .get_columns()
            .iter()
            .map(|column| {
                let key = (*column.column_type(), column.index());
                (key, column_idx[&key])
            })
            .collect();
        let mut preprocess_collector = PreprocessCollector {
            k: *k,
            num_instances,
            fixeds: vec![vec![F::ZERO.into(); 1 << k]; cs.num_fixed_columns()],
            permutation: Permutation::new(permutation_column_idx),
            selectors: vec![vec![false; 1 << k]; cs.num_selectors()],
            row_mapping,
        };

        C::FloorPlanner::synthesize(
            &mut preprocess_collector,
            circuit,
            config.clone(),
            constants.clone(),
        )
        .map_err(|err| crate::Error::InvalidSnark(format!("Synthesize failure: {err:?}")))?;

        circuit_info.preprocess_polys = chain![
            batch_invert_assigned(preprocess_collector.fixeds),
            preprocess_collector.selectors.into_iter().map(|selectors| {
                selectors
                    .into_iter()
                    .map(|selector| if selector { F::ONE } else { F::ZERO })
                    .collect()
            }),
        ]
        .collect();
        circuit_info.permutations = preprocess_collector.permutation.into_cycles();

        Ok(circuit_info)
    }

    fn instances(&self) -> &[Vec<F>] {
        &self.instances
    }

    fn synthesize(&self, phase: usize, challenges: &[F]) -> Result<Vec<Vec<F>>, crate::Error> {
        let instances = self.instances.iter().map(Vec::as_slice).collect_vec();
        let mut witness_collector = WitnessCollector {
            k: self.k,
            phase: phase as u8,
            advice_idx_in_phase: &self.advice_idx_in_phase,
            challenge_idx: &self.challenge_idx,
            instances: instances.as_slice(),
            advices: vec![vec![F::ZERO.into(); 1 << self.k]; self.num_witness_polys[phase]],
            challenges,
            row_mapping: &self.row_mapping,
        };

        C::FloorPlanner::synthesize(
            &mut witness_collector,
            &self.circuit,
            self.config.clone(),
            self.constants.clone(),
        )
        .map_err(|err| crate::Error::InvalidSnark(format!("Synthesize failure: {err:?}")))?;

        Ok(batch_invert_assigned(witness_collector.advices))
    }
}
