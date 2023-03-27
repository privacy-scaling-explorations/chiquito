use std::{collections::HashMap, rc::Rc};

use crate::ast::{Circuit, ForwardSignal, InternalSignal, StepType};

use super::Column;

#[derive(Clone, Debug)]
pub struct SignalPlacement {
    pub column: Column,
    pub rotation: u32,
}

#[derive(Debug)]
pub struct StepPlacement {
    height: u32,
    signals: HashMap<InternalSignal, SignalPlacement>,
}

#[derive(Debug)]
pub struct Placement<F, StepArgs> {
    pub forward: HashMap<ForwardSignal, SignalPlacement>,
    pub steps: HashMap<Rc<StepType<F, StepArgs>>, StepPlacement>,
    pub columns: Vec<Column>,
}

impl<F, StepArgs> Placement<F, StepArgs> {
    pub fn get_forward_placement(&self, forward: &ForwardSignal) -> SignalPlacement {
        self.forward
            .get(forward)
            .expect("forward signal not found")
            .clone()
    }

    pub fn find_internal_signal_placement(
        &self,
        step: &StepType<F, StepArgs>,
        signal: &InternalSignal,
    ) -> SignalPlacement {
        self.steps
            .get(step)
            .expect("step not found")
            .signals
            .get(signal)
            .expect("signal not found")
            .clone()
    }

    pub fn step_height(&self, step: &StepType<F, StepArgs>) -> u32 {
        self.steps.get(step).expect("step not found").height
    }
}

pub trait CellManager {
    fn place<F, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> Placement<F, StepArgs>;
}

pub struct SimpleCellManager {}

impl CellManager for SimpleCellManager {
    fn place<F, TraceArgs, StepArgs>(
        &self,
        sc: &Circuit<F, TraceArgs, StepArgs>,
    ) -> Placement<F, StepArgs> {
        let mut placement = Placement::<F, StepArgs> {
            forward: HashMap::new(),
            steps: HashMap::new(),
            columns: Vec::new(),
        };

        let mut forward_signals: u32 = 0;

        for forward_signal in sc.forward_signals.iter() {
            let column = Column::new("scm forward");
            placement.columns.push(column.clone());

            placement.forward.insert(
                forward_signal.clone(),
                SignalPlacement {
                    column: column,
                    rotation: 0,
                },
            );

            forward_signals += 1;
        }

        let mut max_internal_width: u32 = 0;

        for step in sc.step_types.values().into_iter() {
            let mut internal_signals: u32 = 0;

            let mut step_placement = StepPlacement {
                height: 1, // This cellmanager always have SuperRows with height 1
                signals: HashMap::new(),
            };

            for signal in step.signals.iter() {
                let column_pos = forward_signals + internal_signals;
                let column = if placement.columns.len() <= column_pos as usize {
                    let column = Column::new("scm forward");
                    placement.columns.push(column.clone());
                    column
                } else {
                    placement.columns[column_pos as usize].clone()
                };

                step_placement.signals.insert(
                    signal.clone(),
                    SignalPlacement {
                        column: column,
                        rotation: 0,
                    },
                );

                internal_signals += 1;
            }

            placement.steps.insert(Rc::clone(step), step_placement);
            max_internal_width = max_internal_width.max(internal_signals);
        }

        placement
    }
}
