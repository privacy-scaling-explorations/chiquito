use pyo3::{
    prelude::*,
    types::{PyLong, PyString},
};

use crate::{
    ast::{
        expr::{query::Queriable, Expr},
        Circuit, Constraint, ExposeOffset, FixedSignal, ForwardSignal, InternalSignal, Lookup,
        SharedSignal, StepType, StepTypeUUID, TransitionConstraint,
    },
    frontend::dsl::StepTypeHandler,
    plonkish::{
        backend::halo2::{chiquito2Halo2, ChiquitoHalo2, ChiquitoHalo2Circuit},
        compiler::{
            cell_manager::SingleRowCellManager, compile, config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::assignments::AssignmentGenerator,
    },
    util::{uuid, UUID},
    wit_gen::{StepInstance, TraceContext, TraceWitness},
};

use core::result::Result;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use serde::de::{self, Deserialize, Deserializer, IgnoredAny, MapAccess, Visitor};
use std::{cell::RefCell, collections::HashMap, fmt, rc::Rc};

type CircuitMapStore = (ChiquitoHalo2<Fr>, Option<AssignmentGenerator<Fr, ()>>);
type CircuitMap = RefCell<HashMap<UUID, CircuitMapStore>>;

thread_local! {
    pub static CIRCUIT_MAP: CircuitMap = RefCell::new(HashMap::new());
}

pub fn chiquito_ast_to_halo2(ast_json: &str) -> UUID {
    let circuit: Circuit<Fr, ()> =
        serde_json::from_str(ast_json).expect("Json deserialization to Circuit failed.");

    let config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
    let (chiquito, assignment_generator) = compile(config, &circuit);
    let chiquito_halo2 = chiquito2Halo2(chiquito);
    let uuid = uuid();

    CIRCUIT_MAP.with(|circuit_map| {
        circuit_map
            .borrow_mut()
            .insert(uuid, (chiquito_halo2, assignment_generator));
    });

    println!("{:?}", uuid);

    uuid
}

fn uuid_to_halo2(uuid: UUID) -> CircuitMapStore {
    CIRCUIT_MAP.with(|circuit_map| {
        let circuit_map = circuit_map.borrow();
        circuit_map.get(&uuid).unwrap().clone()
    })
}

pub fn chiquito_halo2_mock_prover(witness_json: &str, ast_id: UUID) {
    let trace_witness: TraceWitness<Fr> =
        serde_json::from_str(witness_json).expect("Json deserialization to TraceWitness failed.");
    let (compiled, assignment_generator) = uuid_to_halo2(ast_id);
    let circuit: ChiquitoHalo2Circuit<_> = ChiquitoHalo2Circuit::new(
        compiled,
        assignment_generator.map(|g| g.generate_with_witness(trace_witness)),
    );

    let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

    let result = prover.verify_par();

    println!("{:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

struct CircuitVisitor;

impl<'de> Visitor<'de> for CircuitVisitor {
    type Value = Circuit<Fr, ()>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct Cricuit")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Circuit<Fr, ()>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut step_types = None;
        let mut forward_signals = None;
        let mut shared_signals = None;
        let mut fixed_signals = None;
        let mut exposed = None;
        let mut annotations = None;
        let mut fixed_assignments = None;
        let mut first_step = None;
        let mut last_step = None;
        let mut num_steps = None;
        let mut q_enable = None;
        let mut id = None;

        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "step_types" => {
                    if step_types.is_some() {
                        return Err(de::Error::duplicate_field("step_types"));
                    }
                    step_types = Some(map.next_value::<HashMap<UUID, StepType<Fr>>>()?);
                }
                "forward_signals" => {
                    if forward_signals.is_some() {
                        return Err(de::Error::duplicate_field("forward_signals"));
                    }
                    forward_signals = Some(map.next_value::<Vec<ForwardSignal>>()?);
                }
                "shared_signals" => {
                    if shared_signals.is_some() {
                        return Err(de::Error::duplicate_field("shared_signals"));
                    }
                    shared_signals = Some(map.next_value::<Vec<SharedSignal>>()?);
                }
                "fixed_signals" => {
                    if fixed_signals.is_some() {
                        return Err(de::Error::duplicate_field("fixed_signals"));
                    }
                    fixed_signals = Some(map.next_value::<Vec<FixedSignal>>()?);
                }
                "exposed" => {
                    if exposed.is_some() {
                        return Err(de::Error::duplicate_field("exposed"));
                    }
                    exposed = Some(map.next_value::<Vec<(Queriable<Fr>, ExposeOffset)>>()?);
                }
                "annotations" => {
                    if annotations.is_some() {
                        return Err(de::Error::duplicate_field("annotations"));
                    }
                    annotations = Some(map.next_value::<HashMap<UUID, String>>()?);
                }
                "fixed_assignments" => {
                    if fixed_assignments.is_some() {
                        return Err(de::Error::duplicate_field("fixed_assignments"));
                    }
                    fixed_assignments =
                        Some(map.next_value::<Option<HashMap<UUID, (Queriable<Fr>, Vec<Fr>)>>>()?);
                }
                "first_step" => {
                    if first_step.is_some() {
                        return Err(de::Error::duplicate_field("first_step"));
                    }
                    first_step = Some(map.next_value::<Option<StepTypeUUID>>()?);
                }
                "last_step" => {
                    if last_step.is_some() {
                        return Err(de::Error::duplicate_field("last_step"));
                    }
                    last_step = Some(map.next_value::<Option<StepTypeUUID>>()?);
                }
                "num_steps" => {
                    if num_steps.is_some() {
                        return Err(de::Error::duplicate_field("num_steps"));
                    }
                    num_steps = Some(map.next_value::<usize>()?);
                }
                "q_enable" => {
                    if q_enable.is_some() {
                        return Err(de::Error::duplicate_field("q_enable"));
                    }
                    q_enable = Some(map.next_value::<bool>()?);
                }
                "id" => {
                    if id.is_some() {
                        return Err(de::Error::duplicate_field("id"));
                    }
                    id = Some(map.next_value()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(
                        &key,
                        &[
                            "step_types",
                            "forward_signals",
                            "shared_signals",
                            "fixed_signals",
                            "exposed",
                            "annotations",
                            "fixed_assignments",
                            "first_step",
                            "last_step",
                            "num_steps",
                            "q_enable",
                            "id",
                        ],
                    ))
                }
            }
        }
        let step_types = step_types
            .ok_or_else(|| de::Error::missing_field("step_types"))?
            .into_iter()
            .map(|(k, v)| (k, Rc::new(v)))
            .collect();
        let forward_signals =
            forward_signals.ok_or_else(|| de::Error::missing_field("forward_signals"))?;
        let shared_signals =
            shared_signals.ok_or_else(|| de::Error::missing_field("shared_signals"))?;
        let fixed_signals =
            fixed_signals.ok_or_else(|| de::Error::missing_field("fixed_signals"))?;
        let exposed = exposed.ok_or_else(|| de::Error::missing_field("exposed"))?;
        let annotations = annotations.ok_or_else(|| de::Error::missing_field("annotations"))?;
        let fixed_assignments = fixed_assignments
            .ok_or_else(|| de::Error::missing_field("fixed_assignments"))?
            .map(|inner| inner.into_values().collect());
        let first_step = first_step.ok_or_else(|| de::Error::missing_field("first_step"))?;
        let last_step = last_step.ok_or_else(|| de::Error::missing_field("last_step"))?;
        let num_steps = num_steps.ok_or_else(|| de::Error::missing_field("num_steps"))?;
        let q_enable = q_enable.ok_or_else(|| de::Error::missing_field("q_enable"))?;
        let id = id.ok_or_else(|| de::Error::missing_field("id"))?;

        Ok(Circuit {
            step_types,
            forward_signals,
            shared_signals,
            fixed_signals,
            halo2_advice: Default::default(),
            halo2_fixed: Default::default(),
            exposed,
            num_steps,
            annotations,
            trace: Some(Rc::new(|_: &mut TraceContext<_>, _: _| {})),
            fixed_assignments,
            first_step,
            last_step,
            q_enable,
            id,
        })
    }
}
struct StepTypeVisitor;

impl<'de> Visitor<'de> for StepTypeVisitor {
    type Value = StepType<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct StepType")
    }

    fn visit_map<A>(self, mut map: A) -> Result<StepType<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut id = None;
        let mut name = None;
        let mut signals = None;
        let mut constraints = None;
        let mut transition_constraints = None;
        let mut lookups = None;
        let mut annotations = None;

        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "id" => {
                    if id.is_some() {
                        return Err(de::Error::duplicate_field("id"));
                    }
                    id = Some(map.next_value()?);
                }
                "name" => {
                    if name.is_some() {
                        return Err(de::Error::duplicate_field("name"));
                    }
                    name = Some(map.next_value::<String>()?);
                }
                "signals" => {
                    if signals.is_some() {
                        return Err(de::Error::duplicate_field("signals"));
                    }
                    signals = Some(map.next_value::<Vec<InternalSignal>>()?);
                }
                "constraints" => {
                    if constraints.is_some() {
                        return Err(de::Error::duplicate_field("constraints"));
                    }
                    constraints = Some(map.next_value::<Vec<Constraint<Fr>>>()?);
                }
                "transition_constraints" => {
                    if transition_constraints.is_some() {
                        return Err(de::Error::duplicate_field("transition_constraints"));
                    }
                    transition_constraints =
                        Some(map.next_value::<Vec<TransitionConstraint<Fr>>>()?);
                }
                "lookups" => {
                    if lookups.is_some() {
                        return Err(de::Error::duplicate_field("lookups"));
                    }
                    lookups = Some(map.next_value::<Vec<Lookup<Fr>>>()?);
                }
                "annotations" => {
                    if annotations.is_some() {
                        return Err(de::Error::duplicate_field("annotations"));
                    }
                    annotations = Some(map.next_value::<HashMap<UUID, String>>()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(
                        &key,
                        &[
                            "id",
                            "name",
                            "signals",
                            "constraints",
                            "transition_constraints",
                            "lookups",
                            "annotations",
                        ],
                    ))
                }
            }
        }
        let id = id.ok_or_else(|| de::Error::missing_field("id"))?;
        let name = name.ok_or_else(|| de::Error::missing_field("name"))?;
        let signals = signals.ok_or_else(|| de::Error::missing_field("signals"))?;
        let constraints = constraints.ok_or_else(|| de::Error::missing_field("constraints"))?;
        let transition_constraints = transition_constraints
            .ok_or_else(|| de::Error::missing_field("transition_constraints"))?;
        let annotations = annotations.ok_or_else(|| de::Error::missing_field("annotations"))?;

        let mut step_type = StepType::<Fr>::new(id, name);
        step_type.signals = signals;
        step_type.constraints = constraints;
        step_type.transition_constraints = transition_constraints;
        step_type.lookups = Default::default();
        step_type.annotations = annotations;

        Ok(step_type)
    }
}

macro_rules! impl_visitor_constraint_transition {
    ($name:ident, $type:ty, $display:expr) => {
        struct $name;

        impl<'de> Visitor<'de> for $name {
            type Value = $type;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str($display)
            }

            fn visit_map<A>(self, mut map: A) -> Result<$type, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut annotation = None;
                let mut expr = None;
                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "annotation" => {
                            if annotation.is_some() {
                                return Err(de::Error::duplicate_field("annotation"));
                            }
                            annotation = Some(map.next_value::<String>()?);
                        }
                        "expr" => {
                            if expr.is_some() {
                                return Err(de::Error::duplicate_field("expr"));
                            }
                            expr = Some(map.next_value::<Expr<Fr>>()?);
                        }
                        _ => return Err(de::Error::unknown_field(&key, &["annotation", "expr"])),
                    }
                }
                let annotation =
                    annotation.ok_or_else(|| de::Error::missing_field("annotation"))?;
                let expr = expr.ok_or_else(|| de::Error::missing_field("expr"))?;
                Ok(Self::Value { annotation, expr })
            }
        }
    };
}

impl_visitor_constraint_transition!(ConstraintVisitor, Constraint<Fr>, "struct Constraint");
impl_visitor_constraint_transition!(
    TransitionConstraintVisitor,
    TransitionConstraint<Fr>,
    "struct TransitionConstraint"
);

struct LookupVisitor;

impl<'de> Visitor<'de> for LookupVisitor {
    type Value = Lookup<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct Lookup")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Lookup<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut annotation = None;
        let mut exprs = None;
        let mut enable = None;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "annotation" => {
                    if annotation.is_some() {
                        return Err(de::Error::duplicate_field("annotation"));
                    }
                    annotation = Some(map.next_value::<String>()?);
                }
                "exprs" => {
                    if exprs.is_some() {
                        return Err(de::Error::duplicate_field("exprs"));
                    }
                    exprs = Some(map.next_value::<Vec<(Constraint<Fr>, Expr<Fr>)>>()?);
                }
                "enable" => {
                    if enable.is_some() {
                        return Err(de::Error::duplicate_field("enable"));
                    }
                    enable = Some(map.next_value::<Option<Constraint<Fr>>>()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(
                        &key,
                        &["annotation", "exprs", "enable"],
                    ))
                }
            }
        }
        let annotation = annotation.ok_or_else(|| de::Error::missing_field("annotation"))?;
        let exprs = exprs.ok_or_else(|| de::Error::missing_field("exprs"))?;
        let enable = enable.ok_or_else(|| de::Error::missing_field("enable"))?;
        Ok(Self::Value {
            annotation,
            exprs,
            enable,
        })
    }
}

struct ExprVisitor;

impl<'de> Visitor<'de> for ExprVisitor {
    type Value = Expr<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("enum Expr")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Expr<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let key: String = map
            .next_key()?
            .ok_or_else(|| de::Error::custom("map is empty"))?;
        match key.as_str() {
            "Const" => map.next_value().map(Expr::Const),
            "Sum" => map.next_value().map(Expr::Sum),
            "Mul" => map.next_value().map(Expr::Mul),
            "Neg" => map.next_value().map(Expr::Neg),
            "Pow" => map.next_value().map(|(expr, pow)| Expr::Pow(expr, pow)),
            "Internal" => map
                .next_value()
                .map(|signal| Expr::Query(Queriable::Internal(signal))),
            "Forward" => map
                .next_value()
                .map(|(signal, rotation)| Expr::Query(Queriable::Forward(signal, rotation))),
            "Shared" => map
                .next_value()
                .map(|(signal, rotation)| Expr::Query(Queriable::Shared(signal, rotation))),
            "Fixed" => map
                .next_value()
                .map(|(signal, rotation)| Expr::Query(Queriable::Fixed(signal, rotation))),
            "StepTypeNext" => map
                .next_value()
                .map(|step_type| Expr::Query(Queriable::StepTypeNext(step_type))),
            _ => Err(de::Error::unknown_variant(
                &key,
                &[
                    "Const",
                    "Sum",
                    "Mul",
                    "Neg",
                    "Pow",
                    "Internal",
                    "Forward",
                    "Shared",
                    "Fixed",
                    "StepTypeNext",
                ],
            )),
        }
    }
}

struct QueriableVisitor;

impl<'de> Visitor<'de> for QueriableVisitor {
    type Value = Queriable<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("enum Queriable")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Queriable<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let key: String = map
            .next_key()?
            .ok_or_else(|| de::Error::custom("map is empty"))?;
        match key.as_str() {
            "Internal" => map.next_value().map(Queriable::Internal),
            "Forward" => map
                .next_value()
                .map(|(signal, rotation)| Queriable::Forward(signal, rotation)),
            "Shared" => map
                .next_value()
                .map(|(signal, rotation)| Queriable::Shared(signal, rotation)),
            "Fixed" => map
                .next_value()
                .map(|(signal, rotation)| Queriable::Fixed(signal, rotation)),
            "StepTypeNext" => map.next_value().map(Queriable::StepTypeNext),
            _ => Err(de::Error::unknown_variant(
                &key,
                &["Internal", "Forward", "Shared", "Fixed", "StepTypeNext"],
            )),
        }
    }
}

struct ExposeOffsetVisitor;

impl<'de> Visitor<'de> for ExposeOffsetVisitor {
    type Value = ExposeOffset;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("enum ExposeOffset")
    }

    fn visit_map<A>(self, mut map: A) -> Result<ExposeOffset, A::Error>
    where
        A: MapAccess<'de>,
    {
        let key: String = map
            .next_key()?
            .ok_or_else(|| de::Error::custom("map is empty"))?;
        match key.as_str() {
            "First" => {
                let _ = map.next_value::<IgnoredAny>()?;
                Ok(ExposeOffset::First)
            }
            "Last" => {
                let _ = map.next_value::<IgnoredAny>()?;
                Ok(ExposeOffset::Last)
            }
            "Step" => map.next_value().map(ExposeOffset::Step),
            _ => Err(de::Error::unknown_variant(&key, &["First", "Last", "Step"])),
        }
    }
}

macro_rules! impl_visitor_internal_fixed_steptypehandler {
    ($name:ident, $type:ty, $display:expr) => {
        struct $name;

        impl<'de> Visitor<'de> for $name {
            type Value = $type;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str($display)
            }

            fn visit_map<A>(self, mut map: A) -> Result<$type, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut id = None;
                let mut annotation = None;
                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "id" => {
                            if id.is_some() {
                                return Err(de::Error::duplicate_field("id"));
                            }
                            id = Some(map.next_value()?);
                        }
                        "annotation" => {
                            if annotation.is_some() {
                                return Err(de::Error::duplicate_field("annotation"));
                            }
                            annotation = Some(map.next_value::<String>()?);
                        }
                        _ => return Err(de::Error::unknown_field(&key, &["id", "annotation"])),
                    }
                }
                let id = id.ok_or_else(|| de::Error::missing_field("id"))?;
                let annotation =
                    annotation.ok_or_else(|| de::Error::missing_field("annotation"))?;
                Ok(<$type>::new_with_id(id, annotation))
            }
        }
    };
}

impl_visitor_internal_fixed_steptypehandler!(
    InternalSignalVisitor,
    InternalSignal,
    "struct InternalSignal"
);
impl_visitor_internal_fixed_steptypehandler!(FixedSignalVisitor, FixedSignal, "struct FixedSignal");
impl_visitor_internal_fixed_steptypehandler!(
    StepTypeHandlerVisitor,
    StepTypeHandler,
    "struct StepTypeHandler"
);

macro_rules! impl_visitor_forward_shared {
    ($name:ident, $type:ty, $display:expr) => {
        struct $name;

        impl<'de> Visitor<'de> for $name {
            type Value = $type;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str($display)
            }

            fn visit_map<A>(self, mut map: A) -> Result<$type, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut id = None;
                let mut phase = None;
                let mut annotation = None;
                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "id" => {
                            if id.is_some() {
                                return Err(de::Error::duplicate_field("id"));
                            }
                            id = Some(map.next_value()?);
                        }
                        "phase" => {
                            if phase.is_some() {
                                return Err(de::Error::duplicate_field("phase"));
                            }
                            phase = Some(map.next_value()?);
                        }
                        "annotation" => {
                            if annotation.is_some() {
                                return Err(de::Error::duplicate_field("annotation"));
                            }
                            annotation = Some(map.next_value::<String>()?);
                        }
                        _ => {
                            return Err(de::Error::unknown_field(
                                &key,
                                &["id", "phase", "annotation"],
                            ))
                        }
                    }
                }
                let id = id.ok_or_else(|| de::Error::missing_field("id"))?;
                let phase = phase.ok_or_else(|| de::Error::missing_field("phase"))?;
                let annotation =
                    annotation.ok_or_else(|| de::Error::missing_field("annotation"))?;
                Ok(<$type>::new_with_id(id, phase, annotation))
            }
        }
    };
}

impl_visitor_forward_shared!(ForwardSignalVisitor, ForwardSignal, "struct ForwardSignal");
impl_visitor_forward_shared!(SharedSignalVisitor, SharedSignal, "struct SharedSignal");

struct TraceWitnessVisitor;

impl<'de> Visitor<'de> for TraceWitnessVisitor {
    type Value = TraceWitness<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct TraceWitness")
    }

    fn visit_map<A>(self, mut map: A) -> Result<TraceWitness<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut step_instances = None;

        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "step_instances" => {
                    if step_instances.is_some() {
                        return Err(de::Error::duplicate_field("step_instances"));
                    }
                    step_instances = Some(map.next_value()?);
                }
                _ => return Err(de::Error::unknown_field(&key, &["step_instances"])),
            }
        }
        let step_instances =
            step_instances.ok_or_else(|| de::Error::missing_field("step_instances"))?;
        Ok(Self::Value { step_instances })
    }
}

struct StepInstanceVisitor;

impl<'de> Visitor<'de> for StepInstanceVisitor {
    type Value = StepInstance<Fr>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct StepInstance")
    }

    fn visit_map<A>(self, mut map: A) -> Result<StepInstance<Fr>, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut step_type_uuid = None;
        let mut assignments = None;

        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "step_type_uuid" => {
                    if step_type_uuid.is_some() {
                        return Err(de::Error::duplicate_field("step_type_uuid"));
                    }
                    step_type_uuid = Some(map.next_value()?);
                }
                "assignments" => {
                    if assignments.is_some() {
                        return Err(de::Error::duplicate_field("assignments"));
                    }
                    assignments = Some(map.next_value::<HashMap<UUID, (Queriable<Fr>, Fr)>>()?);
                }
                _ => {
                    return Err(de::Error::unknown_field(
                        &key,
                        &["step_type_uuid", "assignments"],
                    ))
                }
            }
        }
        let step_type_uuid =
            step_type_uuid.ok_or_else(|| de::Error::missing_field("step_type_uuid"))?;

        let assignments: HashMap<Queriable<Fr>, Fr> = assignments
            .ok_or_else(|| de::Error::missing_field("assignments"))?
            .into_values()
            .collect();

        Ok(Self::Value {
            step_type_uuid,
            assignments,
        })
    }
}

macro_rules! impl_deserialize {
    ($name:ident, $type:ty) => {
        impl<'de> Deserialize<'de> for $type {
            fn deserialize<D>(deserializer: D) -> Result<$type, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.deserialize_map($name)
            }
        }
    };
}

impl_deserialize!(ExprVisitor, Expr<Fr>);
impl_deserialize!(QueriableVisitor, Queriable<Fr>);
impl_deserialize!(ExposeOffsetVisitor, ExposeOffset);
impl_deserialize!(InternalSignalVisitor, InternalSignal);
impl_deserialize!(FixedSignalVisitor, FixedSignal);
impl_deserialize!(ForwardSignalVisitor, ForwardSignal);
impl_deserialize!(SharedSignalVisitor, SharedSignal);
impl_deserialize!(StepTypeHandlerVisitor, StepTypeHandler);
impl_deserialize!(ConstraintVisitor, Constraint<Fr>);
impl_deserialize!(TransitionConstraintVisitor, TransitionConstraint<Fr>);
impl_deserialize!(StepTypeVisitor, StepType<Fr>);
impl_deserialize!(TraceWitnessVisitor, TraceWitness<Fr>);
impl_deserialize!(StepInstanceVisitor, StepInstance<Fr>);
impl_deserialize!(LookupVisitor, Lookup<Fr>);

impl<'de> Deserialize<'de> for Circuit<Fr, ()> {
    fn deserialize<D>(deserializer: D) -> Result<Circuit<Fr, ()>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(CircuitVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_trace_witness() {
        let json = r#"
        {
            "step_instances": [
                {
                    "step_type_uuid": 270606747459021742275781620564109167114,
                    "assignments": {
                        "270606737951642240564318377467548666378": [
                            {
                                "Forward": [
                                    {
                                        "id": 270606737951642240564318377467548666378,
                                        "phase": 0,
                                        "annotation": "a"
                                    },
                                    false
                                ]
                            },
                            [
                                55,
                                0,
                                0,
                                0
                            ]
                        ],
                        "270606743497613616562965561253747624458": [
                            {
                                "Forward": [
                                    {
                                        "id": 270606743497613616562965561253747624458,
                                        "phase": 0,
                                        "annotation": "b"
                                    },
                                    false
                                ]
                            },
                            [
                                89,
                                0,
                                0,
                                0
                            ]
                        ],
                        "270606753004993118272949371872716917258": [
                            {
                                "Internal": {
                                    "id": 270606753004993118272949371872716917258,
                                    "annotation": "c"
                                }
                            },
                            [
                                144,
                                0,
                                0,
                                0
                            ]
                        ]
                    }
                },
                {
                    "step_type_uuid": 270606783111694873693576112554652600842,
                    "assignments": {
                        "270606737951642240564318377467548666378": [
                            {
                                "Forward": [
                                    {
                                        "id": 270606737951642240564318377467548666378,
                                        "phase": 0,
                                        "annotation": "a"
                                    },
                                    false
                                ]
                            },
                            [
                                89,
                                0,
                                0,
                                0
                            ]
                        ],
                        "270606743497613616562965561253747624458": [
                            {
                                "Forward": [
                                    {
                                        "id": 270606743497613616562965561253747624458,
                                        "phase": 0,
                                        "annotation": "b"
                                    },
                                    false
                                ]
                            },
                            [
                                144,
                                0,
                                0,
                                0
                            ]
                        ],
                        "270606786280821374261518951164072823306": [
                            {
                                "Internal": {
                                    "id": 270606786280821374261518951164072823306,
                                    "annotation": "c"
                                }
                            },
                            [
                                233,
                                0,
                                0,
                                0
                            ]
                        ]
                    }
                }
            ]
        }
        "#;
        let trace_witness: TraceWitness<Fr> = serde_json::from_str(json).unwrap();
        println!("{:?}", trace_witness);
    }

    #[test]
    fn test_expose_offset() {
        let mut json = r#"
        {
            "Step": 1
        }
        "#;
        let _: ExposeOffset = serde_json::from_str(json).unwrap();
        json = r#"
        {
            "Last": -1
        }
        "#;
        let _: ExposeOffset = serde_json::from_str(json).unwrap();
        json = r#"
        {
            "First": 1
        }
        "#;
        let _: ExposeOffset = serde_json::from_str(json).unwrap();
    }

    #[test]
    fn test_circuit() {
        let json = r#"
        {
            "step_types": {
                "258869595755756204079859764249309612554": {
                    "id": 258869595755756204079859764249309612554,
                    "name": "fibo_first_step",
                    "signals": [
                        {
                            "id": 258869599717164329791616633222308956682,
                            "annotation": "c"
                        }
                    ],
                    "constraints": [
                        {
                            "annotation": "(a == 1)",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869580702405326369584955980151130634,
                                                "phase": 0,
                                                "annotation": "a"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Const": [
                                                1,
                                                0,
                                                0,
                                                0
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(b == 1)",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Const": [
                                                1,
                                                0,
                                                0,
                                                0
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "((a + b) == c)",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869580702405326369584955980151130634,
                                                "phase": 0,
                                                "annotation": "a"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Internal": {
                                                "id": 258869599717164329791616633222308956682,
                                                "annotation": "c"
                                            }
                                        }
                                    }
                                ]
                            }
                        }
                    ],
                    "transition_constraints": [
                        {
                            "annotation": "(b == next(a))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869580702405326369584955980151130634,
                                                    "phase": 0,
                                                    "annotation": "a"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(c == next(b))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Internal": {
                                            "id": 258869599717164329791616633222308956682,
                                            "annotation": "c"
                                        }
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869587040658327507391136965088381450,
                                                    "phase": 0,
                                                    "annotation": "b"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(n == next(n))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869589417503202934383108674030275082,
                                                "phase": 0,
                                                "annotation": "n"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869589417503202934383108674030275082,
                                                    "phase": 0,
                                                    "annotation": "n"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        }
                    ],
                    "lookups": [],
                    "annotations": {
                        "258869599717164329791616633222308956682": "c"
                    }
                },
                "258869628239302834927102989021255174666": {
                    "id": 258869628239302834927102989021255174666,
                    "name": "fibo_step",
                    "signals": [
                        {
                            "id": 258869632200710960639812650790420089354,
                            "annotation": "c"
                        }
                    ],
                    "constraints": [
                        {
                            "annotation": "((a + b) == c)",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869580702405326369584955980151130634,
                                                "phase": 0,
                                                "annotation": "a"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Internal": {
                                                "id": 258869632200710960639812650790420089354,
                                                "annotation": "c"
                                            }
                                        }
                                    }
                                ]
                            }
                        }
                    ],
                    "transition_constraints": [
                        {
                            "annotation": "(b == next(a))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869580702405326369584955980151130634,
                                                    "phase": 0,
                                                    "annotation": "a"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(c == next(b))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Internal": {
                                            "id": 258869632200710960639812650790420089354,
                                            "annotation": "c"
                                        }
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869587040658327507391136965088381450,
                                                    "phase": 0,
                                                    "annotation": "b"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(n == next(n))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869589417503202934383108674030275082,
                                                "phase": 0,
                                                "annotation": "n"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869589417503202934383108674030275082,
                                                    "phase": 0,
                                                    "annotation": "n"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        }
                    ],
                    "lookups": [],
                    "annotations": {
                        "258869632200710960639812650790420089354": "c"
                    }
                },
                "258869646461780213207493341245063432714": {
                    "id": 258869646461780213207493341245063432714,
                    "name": "padding",
                    "signals": [],
                    "constraints": [],
                    "transition_constraints": [
                        {
                            "annotation": "(b == next(b))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869587040658327507391136965088381450,
                                                "phase": 0,
                                                "annotation": "b"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869587040658327507391136965088381450,
                                                    "phase": 0,
                                                    "annotation": "b"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        },
                        {
                            "annotation": "(n == next(n))",
                            "expr": {
                                "Sum": [
                                    {
                                        "Forward": [
                                            {
                                                "id": 258869589417503202934383108674030275082,
                                                "phase": 0,
                                                "annotation": "n"
                                            },
                                            false
                                        ]
                                    },
                                    {
                                        "Neg": {
                                            "Forward": [
                                                {
                                                    "id": 258869589417503202934383108674030275082,
                                                    "phase": 0,
                                                    "annotation": "n"
                                                },
                                                true
                                            ]
                                        }
                                    }
                                ]
                            }
                        }
                    ],
                    "lookups": [],
                    "annotations": {}
                }
            },
            "forward_signals": [
                {
                    "id": 258869580702405326369584955980151130634,
                    "phase": 0,
                    "annotation": "a"
                },
                {
                    "id": 258869587040658327507391136965088381450,
                    "phase": 0,
                    "annotation": "b"
                },
                {
                    "id": 258869589417503202934383108674030275082,
                    "phase": 0,
                    "annotation": "n"
                }
            ],
            "shared_signals": [],
            "fixed_signals": [],
            "exposed": [
                [
                    {
                        "Forward": [
                            {
                                "id": 258869587040658327507391136965088381450,
                                "phase": 0,
                                "annotation": "b"
                            },
                            false
                        ]
                    },
                    {
                        "Last": -1
                    }
                ],
                [
                    {
                        "Forward": [
                            {
                                "id": 258869589417503202934383108674030275082,
                                "phase": 0,
                                "annotation": "n"
                            },
                            false
                        ]
                    },
                    {
                        "Last": -1
                    }
                ]
            ],
            "annotations": {
                "258869580702405326369584955980151130634": "a",
                "258869587040658327507391136965088381450": "b",
                "258869589417503202934383108674030275082": "n",
                "258869595755756204079859764249309612554": "fibo_first_step",
                "258869628239302834927102989021255174666": "fibo_step",
                "258869646461780213207493341245063432714": "padding"
            },
            "fixed_assignments": null,
            "first_step": 258869595755756204079859764249309612554,
            "last_step": 258869646461780213207493341245063432714,
            "num_steps": 10,
            "q_enable": true,
            "id": 258867373405797678961444396351437277706
        }
        "#;
        let circuit: Circuit<Fr, ()> = serde_json::from_str(json).unwrap();
        println!("{:?}", circuit);
    }

    #[test]
    fn test_step_type() {
        let json = r#"
        {
            "id":1,
            "name":"fibo",
            "signals":[
                {
                    "id":1,
                    "annotation":"a"
                },
                {
                    "id":2,
                    "annotation":"b"
                }
            ],
            "constraints":[
                {
                    "annotation":"constraint",
                    "expr":{
                        "Sum":[
                            {
                                "Const":[1, 0, 0, 0]
                            },
                            {
                                "Mul":[
                                    {
                                        "Internal":{
                                            "id":3,
                                            "annotation":"c"
                                        }
                                    },
                                    {
                                        "Const":[3, 0, 0, 0]
                                    }
                                ]
                            }
                        ]
                    }
                },
                {
                    "annotation":"constraint",
                    "expr":{
                        "Sum":[
                            {
                                "Const":[1, 0, 0, 0]
                            },
                            {
                                "Mul":[
                                    {
                                        "Shared":[
                                            {
                                                "id":4,
                                                "phase":2,
                                                "annotation":"d"
                                            },
                                            1
                                        ]
                                    },
                                    {
                                        "Const":[3, 0, 0, 0]
                                    }
                                ]
                            }
                        ]
                    }
                }
            ],
            "transition_constraints":[
                {
                    "annotation":"trans",
                    "expr":{
                        "Sum":[
                            {
                                "Const":[1, 0, 0, 0]
                            },
                            {
                                "Mul":[
                                    {
                                        "Forward":[
                                            {
                                                "id":5,
                                                "phase":1,
                                                "annotation":"e"
                                            },
                                            true
                                        ]
                                    },
                                    {
                                        "Const":[3, 0, 0, 0]
                                    }
                                ]
                            }
                        ]
                    }
                },
                {
                    "annotation":"trans",
                    "expr":{
                        "Sum":[
                            {
                                "Const":[1, 0, 0, 0]
                            },
                            {
                                "Mul":[
                                    {
                                        "Fixed":[
                                            {
                                                "id":6,
                                                "annotation":"e"
                                            },
                                            2
                                        ]
                                    },
                                    {
                                        "Const":[3, 0, 0, 0]
                                    }
                                ]
                            }
                        ]
                    }
                }
            ],
            "annotations":{
                "5":"a",
                "6":"b",
                "7":"c"
            }
        }
        "#;
        let step_type: StepType<Fr> = serde_json::from_str(json).unwrap();
        println!("{:?}", step_type);
    }

    #[test]
    fn test_constraint() {
        let json = r#"
        {"annotation": "constraint",
        "expr": 
        {
            "Sum": [
                {
                "Internal": {
                    "id": 27,
                    "annotation": "a"
                }
                },
                {
                "Fixed": [
                    {
                        "id": 28,
                        "annotation": "b"
                    },
                    1
                ]
                },
                {
                "Shared": [
                    {
                        "id": 29,
                        "phase": 1,
                        "annotation": "c"
                    },
                    2
                ]
                },
                {
                "Forward": [
                    {
                        "id": 30,
                        "phase": 2,
                        "annotation": "d"
                    },
                    true
                ]
                },
                {
                "StepTypeNext": {
                    "id": 31,
                    "annotation": "e"
                }
                },
                {
                "Const": [3, 0, 0, 0]
                },
                {
                "Mul": [
                    {
                    "Const": [4, 0, 0, 0]
                    },
                    {
                    "Const": [5, 0, 0, 0]
                    }
                ]
                },
                {
                "Neg": {
                    "Const": [2, 0, 0, 0]
                }
                },
                {
                "Pow": [
                    {
                    "Const": [3, 0, 0, 0]
                    },
                    4
                ]
                }
            ]
            }
        }"#;
        let constraint: Constraint<Fr> = serde_json::from_str(json).unwrap();
        println!("{:?}", constraint);
        let transition_constraint: TransitionConstraint<Fr> = serde_json::from_str(json).unwrap();
        println!("{:?}", transition_constraint);
    }

    #[test]
    fn test_expr() {
        let json = r#"
        {
            "Sum": [
                {
                "Internal": {
                    "id": 27,
                    "annotation": "a"
                }
                },
                {
                "Fixed": [
                    {
                        "id": 28,
                        "annotation": "b"
                    },
                    1
                ]
                },
                {
                "Shared": [
                    {
                        "id": 29,
                        "phase": 1,
                        "annotation": "c"
                    },
                    2
                ]
                },
                {
                "Forward": [
                    {
                        "id": 30,
                        "phase": 2,
                        "annotation": "d"
                    },
                    true
                ]
                },
                {
                "StepTypeNext": {
                    "id": 31,
                    "annotation": "e"
                }
                },
                {
                "Const": [3, 0, 0, 0]
                },
                {
                "Mul": [
                    {
                    "Const": [4, 0, 0, 0]
                    },
                    {
                    "Const": [5, 0, 0, 0]
                    }
                ]
                },
                {
                "Neg": {
                    "Const": [2, 0, 0, 0]
                }
                },
                {
                "Pow": [
                    {
                    "Const": [3, 0, 0, 0]
                    },
                    4
                ]
                }
            ]
            }"#;
        let expr: Expr<Fr> = serde_json::from_str(json).unwrap();
        println!("{:?}", expr);
    }
}

#[pyfunction]
fn convert_and_print_ast(json: &PyString) {
    let circuit: Circuit<Fr, ()> =
        serde_json::from_str(json.to_str().expect("PyString convertion failed."))
            .expect("Json deserialization to Circuit failed.");
    println!("{:?}", circuit);
}

#[pyfunction]
fn convert_and_print_trace_witness(json: &PyString) {
    let trace_witness: TraceWitness<Fr> =
        serde_json::from_str(json.to_str().expect("PyString convertion failed."))
            .expect("Json deserialization to TraceWitness failed.");
    println!("{:?}", trace_witness);
}

#[pyfunction]
fn ast_to_halo2(json: &PyString) -> u128 {
    let uuid = chiquito_ast_to_halo2(json.to_str().expect("PyString convertion failed."));

    uuid
}

#[pyfunction]
fn halo2_mock_prover(witness_json: &PyString, ast_uuid: &PyLong) {
    chiquito_halo2_mock_prover(
        witness_json.to_str().expect("PyString convertion failed."),
        ast_uuid.extract().expect("PyLong convertion failed."),
    );
}

#[pymodule]
fn rust_chiquito(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(convert_and_print_ast, m)?)?;
    m.add_function(wrap_pyfunction!(convert_and_print_trace_witness, m)?)?;
    m.add_function(wrap_pyfunction!(ast_to_halo2, m)?)?;
    m.add_function(wrap_pyfunction!(halo2_mock_prover, m)?)?;
    Ok(())
}
