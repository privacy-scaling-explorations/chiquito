use std::{collections::HashMap, fmt::Debug};

use crate::ast::{FixedSignal, ForwardSignal, InternalSignal, SharedSignal, StepTypeUUID};

use super::{Column, CompilationUnit};

#[derive(Clone, Debug)]
pub struct SignalPlacement {
    pub column: Column,
    pub rotation: i32,
}

impl SignalPlacement {
    pub fn new(column: Column, rotation: i32) -> Self {
        Self { column, rotation }
    }
}

impl From<(Column, i32)> for SignalPlacement {
    fn from((column, rotation): (Column, i32)) -> Self {
        SignalPlacement::new(column, rotation)
    }
}

impl From<SignalPlacement> for (Column, i32) {
    fn from(placement: SignalPlacement) -> Self {
        (placement.column, placement.rotation)
    }
}

#[derive(Debug, Clone)]
pub struct StepPlacement {
    height: u32,
    signals: HashMap<InternalSignal, SignalPlacement>,
}

#[derive(Debug, Clone, Default)]
pub struct Placement {
    pub forward: HashMap<ForwardSignal, SignalPlacement>,
    pub shared: HashMap<SharedSignal, SignalPlacement>,
    pub fixed: HashMap<FixedSignal, SignalPlacement>,
    pub steps: HashMap<StepTypeUUID, StepPlacement>,
    pub columns: Vec<Column>,

    pub base_height: u32,
}

impl Placement {
    pub fn get_forward_placement(&self, forward: &ForwardSignal) -> Option<SignalPlacement> {
        self.forward.get(forward).cloned()
    }

    pub fn get_shared_placement(&self, shared: &SharedSignal) -> Option<SignalPlacement> {
        self.shared.get(shared).cloned()
    }

    pub fn get_fixed_placement(&self, fixed: &FixedSignal) -> Option<SignalPlacement> {
        self.fixed.get(fixed).cloned()
    }

    pub fn find_internal_signal_placement(
        &self,
        step_uuid: StepTypeUUID,
        signal: &InternalSignal,
    ) -> SignalPlacement {
        self.steps
            .get(&step_uuid)
            .expect("step not found")
            .signals
            .get(signal)
            .expect("signal not found")
            .clone()
    }

    pub fn step_height(&self, step_uuid: StepTypeUUID) -> u32 {
        self.steps.get(&step_uuid).expect("step not found").height
    }

    pub fn first_step_height(&self) -> u32 {
        if let Some(step) = self.steps.values().next() {
            step.height
        } else {
            self.base_height
        }
    }

    // Returns true iff all steps have the same height.
    pub fn same_height(&self) -> bool {
        if self.steps.is_empty() {
            return true;
        }

        let first = self.steps.values().next().unwrap().height;

        self.steps.values().all(|step| step.height == first)
    }
}

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
            columns: Vec::new(),
            base_height: 1,
        };

        let mut forward_signals: u32 = 0;

        for forward_signal in unit.forward_signals.iter() {
            let column = if let Some(annotation) = unit.annotations.get(&forward_signal.uuid()) {
                Column::advice(
                    format!("srcm forward {}", annotation),
                    forward_signal.phase(),
                )
            } else {
                Column::advice("srcm forward", forward_signal.phase())
            };

            placement.columns.push(column.clone());

            placement.forward.insert(
                *forward_signal,
                SignalPlacement {
                    column,
                    rotation: 0,
                },
            );

            forward_signals += 1;
        }

        let mut shared_signals: u32 = 0;

        for shared_signal in unit.shared_signals.iter() {
            let column = if let Some(annotation) = unit.annotations.get(&shared_signal.uuid()) {
                Column::advice(format!("srcm shared {}", annotation), shared_signal.phase())
            } else {
                Column::advice("srcm shared", shared_signal.phase())
            };

            placement.columns.push(column.clone());

            placement.shared.insert(
                *shared_signal,
                SignalPlacement {
                    column,
                    rotation: 0,
                },
            );

            shared_signals += 1;
        }

        let mut fixed_signals: u32 = 0;

        for fixed_signal in unit.fixed_signals.iter() {
            let column = if let Some(annotation) = unit.annotations.get(&fixed_signal.uuid()) {
                Column::fixed(format!("srcm fixed {}", annotation))
            } else {
                Column::fixed("srcm fixed")
            };

            placement.columns.push(column.clone());

            placement.fixed.insert(
                *fixed_signal,
                SignalPlacement {
                    column,
                    rotation: 0,
                },
            );

            fixed_signals += 1;
        }

        let mut max_internal_width: u32 = 0;

        for step in unit.step_types.values() {
            let mut internal_signals: u32 = 0;

            let mut step_placement = StepPlacement {
                height: 1, // This cellmanager always have SuperRows with height 1
                signals: HashMap::new(),
            };

            for signal in step.signals.iter() {
                let column_pos =
                    forward_signals + shared_signals + fixed_signals + internal_signals;
                let column = if placement.columns.len() <= column_pos as usize {
                    let column = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                        Column::advice(format!("srcm internal signal {}", annotation), 0)
                    } else {
                        Column::advice("srcm internal signal", 0)
                    };

                    placement.columns.push(column.clone());
                    column
                } else {
                    placement.columns[column_pos as usize].clone()
                };

                step_placement.signals.insert(
                    *signal,
                    SignalPlacement {
                        column,
                        rotation: 0,
                    },
                );

                internal_signals += 1;
            }

            placement.steps.insert(step.uuid(), step_placement);
            max_internal_width = max_internal_width.max(internal_signals);
        }

        unit.columns.extend_from_slice(&placement.columns);
        unit.placement = placement;
    }
}

#[derive(Debug, Default, Clone)]
pub struct MaxWidthCellManager {
    max_width: usize,
    same_height: bool,
}

impl MaxWidthCellManager {
    pub fn new(max_width: usize, same_height: bool) -> Self {
        Self {
            max_width,
            same_height,
        }
    }
}

impl CellManager for MaxWidthCellManager {
    fn place<F>(&self, unit: &mut CompilationUnit<F>) {
        if (!unit.shared_signals.is_empty() || !unit.fixed_signals.is_empty()) && !self.same_height
        {
            panic!("Shared signals and fixed signals are not supported for MaxWidthCellManager, which might return steps with variable heights.");
        }

        let mut placement = Placement {
            forward: HashMap::new(),
            shared: HashMap::new(),
            fixed: HashMap::new(),
            steps: HashMap::new(),
            columns: Vec::new(),
            base_height: 0,
        };

        let mut forward_signal_column: usize = 0;
        let mut forward_signal_row: usize = 0;

        for forward_signal in unit.forward_signals.iter() {
            let column = if placement.columns.len() <= forward_signal_column {
                let column = if let Some(annotation) = unit.annotations.get(&forward_signal.uuid())
                {
                    Column::advice(format!("mwcm forward signal {}", annotation), 0)
                } else {
                    Column::advice("mwcm forward signal", 0)
                };

                placement.columns.push(column.clone());
                column
            } else {
                placement.columns[forward_signal_column].clone()
            };

            placement.forward.insert(
                *forward_signal,
                SignalPlacement {
                    column,
                    rotation: forward_signal_row as i32,
                },
            );

            forward_signal_column += 1;
            if forward_signal_column >= self.max_width {
                forward_signal_column = 0;
                forward_signal_row += 1;
            }
        }

        placement.base_height = if forward_signal_column != 0 {
            forward_signal_row + 1
        } else {
            forward_signal_row
        } as u32;

        for step in unit.step_types.values() {
            let mut step_placement = StepPlacement {
                height: if forward_signal_column > 0 {
                    (forward_signal_row + 1) as u32
                } else {
                    forward_signal_row as u32
                },
                signals: HashMap::new(),
            };

            let mut internal_signal_column = forward_signal_column;
            let mut internal_signal_row = forward_signal_row;

            for signal in step.signals.iter() {
                let column = if placement.columns.len() <= internal_signal_column {
                    let column = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                        Column::advice(format!("mwcm internal signal {}", annotation), 0)
                    } else {
                        Column::advice("mwcm internal signal", 0)
                    };

                    placement.columns.push(column.clone());
                    column
                } else {
                    placement.columns[internal_signal_column].clone()
                };

                step_placement.signals.insert(
                    *signal,
                    SignalPlacement {
                        column,
                        rotation: internal_signal_row as i32,
                    },
                );

                step_placement.height = (internal_signal_row + 1) as u32;

                internal_signal_column += 1;
                if internal_signal_column >= self.max_width {
                    internal_signal_column = 0;
                    internal_signal_row += 1;
                }
            }

            placement.steps.insert(step.uuid(), step_placement);
        }

        if self.same_height {
            let height = placement
                .steps
                .values()
                .map(|step| step.height)
                .max()
                .unwrap_or(0);

            placement
                .steps
                .iter_mut()
                .for_each(|(_, step)| step.height = height);
        }

        unit.columns.extend_from_slice(&placement.columns);
        unit.placement = placement;
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{
        ast::{ForwardSignal, StepType},
        plonkish::compiler::CompilationUnit,
    };

    use super::{CellManager, MaxWidthCellManager};

    #[test]
    fn test_max_width_cm_2_columns() {
        let mut unit = CompilationUnit::<()> {
            forward_signals: vec![
                ForwardSignal::new_with_phase(0, "a".to_string()),
                ForwardSignal::new_with_phase(0, "a".to_string()),
            ],
            ..Default::default()
        };

        let mut step1 = StepType::new(1500, "step1".to_string());
        step1.add_signal("c1");
        step1.add_signal("d");
        step1.add_signal("e");
        let mut step2 = StepType::new(1501, "step2".to_string());
        step2.add_signal("c2");

        let step1 = Rc::new(step1);
        let step2 = Rc::new(step2);

        unit.step_types.insert(1500, Rc::clone(&step1));
        unit.step_types.insert(1501, Rc::clone(&step2));

        // forward signals: a, b; step1 internal: c1, d, e; step2 internal c2

        let cm = MaxWidthCellManager {
            max_width: 2,
            same_height: false,
        };

        cm.place(&mut unit);

        assert_eq!(unit.placement.columns.len(), 2);
        assert_eq!(unit.placement.forward.len(), 2);
        assert_eq!(
            unit.placement
                .steps
                .get(&step1.uuid())
                .expect("should be there")
                .height,
            3
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step1.uuid())
                .expect("should be there")
                .signals
                .len(),
            3
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step2.uuid())
                .expect("should be there")
                .height,
            2
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step2.uuid())
                .expect("should be there")
                .signals
                .len(),
            1
        );
    }

    #[test]
    fn test_max_width_cm_2_columns_same_height() {
        let mut unit = CompilationUnit::<()> {
            forward_signals: vec![
                ForwardSignal::new_with_phase(0, "a".to_string()),
                ForwardSignal::new_with_phase(0, "a".to_string()),
            ],
            ..Default::default()
        };

        let mut step1 = StepType::new(1500, "step1".to_string());
        step1.add_signal("c1");
        step1.add_signal("d");
        step1.add_signal("e");
        let mut step2 = StepType::new(1501, "step2".to_string());
        step2.add_signal("c2");

        let step1 = Rc::new(step1);
        let step2 = Rc::new(step2);

        unit.step_types.insert(1500, Rc::clone(&step1));
        unit.step_types.insert(1501, Rc::clone(&step2));

        // forward signals: a, b; step1 internal: c1, d, e; step2 internal c2

        let cm = MaxWidthCellManager {
            max_width: 2,
            same_height: true,
        };

        cm.place(&mut unit);

        assert_eq!(unit.placement.columns.len(), 2);
        assert_eq!(unit.placement.forward.len(), 2);
        assert_eq!(
            unit.placement
                .steps
                .get(&step1.uuid())
                .expect("should be there")
                .height,
            3
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step1.uuid())
                .expect("should be there")
                .signals
                .len(),
            3
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step2.uuid())
                .expect("should be there")
                .height,
            3 // it is 3 to be the same height, but one row is unused
        );
        assert_eq!(
            unit.placement
                .steps
                .get(&step2.uuid())
                .expect("should be there")
                .signals
                .len(),
            1
        );
    }
}
