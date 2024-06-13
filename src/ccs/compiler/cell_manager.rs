use super::CompilationUnit;
use std::{collections::HashMap, fmt::Debug};

use crate::util::UUID;
pub trait CellManager: Clone {
    fn place<F>(&self, unit: &mut CompilationUnit<F>);
}

#[derive(Debug, Default, Clone)]
pub struct SingleRowCellManager {}

impl CellManager for SingleRowCellManager {
    fn place<F>(&self, unit: &mut CompilationUnit<F>) {
        let mut placement = Placement {
            forward: HashMap::new(),
            shared: HashMap::new(),
            fixed: HashMap::new(),
            steps: HashMap::new(),
            base_height: 0,
        };

        let mut forward_signals: u32 = 0;
        for signal in unit.forward_signals.iter() {
            placement.forward.insert(
                signal.uuid(),
                SignalPlacement::new(signal.uuid(), signal.annotation(), forward_signals),
            );
            forward_signals += 1;
        }

        let mut shared_signals: u32 = 0;
        for signal in unit.shared_signals.iter() {
            placement.shared.insert(
                signal.uuid(),
                SignalPlacement::new(
                    signal.uuid(),
                    signal.annotation(),
                    forward_signals + shared_signals,
                ),
            );
            shared_signals += 1;
        }

        let mut fixed_signals: u32 = 0;
        for signal in unit.fixed_signals.iter() {
            placement.fixed.insert(
                signal.uuid(),
                SignalPlacement::new(
                    signal.uuid(),
                    signal.annotation(),
                    forward_signals + shared_signals + fixed_signals,
                ),
            );
            fixed_signals += 1;
        }

        placement.base_height = forward_signals + shared_signals + fixed_signals;

        for step in unit.step_types.values() {
            let mut internal_signals: u32 = 0;
            let mut step_placement = StepPlacement::new(0, HashMap::new());
            for signal in step.signals.iter() {
                step_placement.signals.insert(
                    signal.uuid(),
                    SignalPlacement::new(signal.uuid(), signal.annotation(), internal_signals),
                );
                internal_signals += 1;
            }
            step_placement.height = internal_signals;
            placement.steps.insert(step.uuid(), step_placement);
        }
        unit.placement = placement;
    }
}

#[derive(Debug, Clone)]
pub struct SignalPlacement {
    id: UUID,
    annotation: String,
    offset: u32,
}

impl SignalPlacement {
    pub fn new(id: UUID, annotation: String, offset: u32) -> Self {
        Self {
            id,
            annotation,
            offset,
        }
    }

    pub fn new_with_id(id: UUID, annotation: String) -> Self {
        Self {
            id,
            annotation,
            offset: 0,
        }
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }

    pub fn annotation(&self) -> String {
        self.annotation.to_string()
    }

    pub fn offset(&self) -> u32 {
        self.offset
    }
}

#[derive(Debug, Clone)]
pub struct StepPlacement {
    height: u32,
    signals: HashMap<UUID, SignalPlacement>,
}

impl StepPlacement {
    pub fn new(height: u32, signals: HashMap<UUID, SignalPlacement>) -> Self {
        Self { height, signals }
    }

    pub fn height(&self) -> u32 {
        self.height
    }

    pub fn signal(&self, uuid: UUID) -> SignalPlacement {
        self.signals.get(&uuid).unwrap().clone()
    }

    pub fn signals(&self) -> HashMap<UUID, SignalPlacement> {
        self.signals.clone()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Placement {
    pub forward: HashMap<UUID, SignalPlacement>,
    pub shared: HashMap<UUID, SignalPlacement>,
    pub fixed: HashMap<UUID, SignalPlacement>,
    pub steps: HashMap<UUID, StepPlacement>,
    pub base_height: u32,
}

impl Placement {
    pub fn step_height(&self, step_uuid: UUID) -> u32 {
        self.steps.get(&step_uuid).expect("step not found").height()
    }

    pub fn step(&self, step_uuid: UUID) -> StepPlacement {
        self.steps.get(&step_uuid).unwrap().clone()
    }

    pub fn forward(&self, forward_uuid: UUID) -> SignalPlacement {
        self.forward.get(&forward_uuid).unwrap().clone()
    }

    pub fn shared(&self, shared_uuid: UUID) -> SignalPlacement {
        self.shared.get(&shared_uuid).unwrap().clone()
    }

    pub fn fixed(&self, fixed_uuid: UUID) -> SignalPlacement {
        self.fixed.get(&fixed_uuid).unwrap().clone()
    }

    pub fn internal(&self, step_uuid: UUID, internal_uuid: UUID) -> SignalPlacement {
        self.steps.get(&step_uuid).unwrap().signal(internal_uuid)
    }
}
