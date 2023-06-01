use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
        VirtualCells,
    },
    poly::Rotation,
};

use crate::{
    ast::{query::Queriable, ForwardSignal, InternalSignal, StepType, ToField},
    compiler::{
        cell_manager::Placement, step_selector::StepSelector, FixedGenContext, TraceContext,
        WitnessGenContext,
    },
    dsl::StepTypeHandler,
    ir::{
        Circuit, Column as cColumn,
        ColumnType::{Advice as cAdvice, Fixed as cFixed, Halo2Advice, Halo2Fixed},
        PolyExpr,
    },
};

