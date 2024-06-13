pub mod cell_manager;
pub mod step_selector;
pub(crate) mod unit;

use std::{hash::Hash, rc::Rc};
use unit::CompilationUnit;

use crate::{
    ccs::ir::{assignments::AssignmentGenerator, circuit::Circuit, Poly, PolyExpr},
    field::Field,
    poly::Expr,
    sbpir::{query::Queriable, ExposeOffset, StepType, PIR, SBPIR as astCircuit},
    wit_gen::{AutoTraceGenerator, TraceGenerator},
};

use cell_manager::CellManager;
use step_selector::StepSelectorBuilder;

use self::cell_manager::SignalPlacement;

#[derive(Clone)]
pub struct CompilerConfig<CM: CellManager, SSB: StepSelectorBuilder> {
    cell_manager: CM,
    step_selector_builder: SSB,
}

pub fn config<CM: CellManager, SSB: StepSelectorBuilder>(
    cell_manager: CM,
    step_selector_builder: SSB,
) -> CompilerConfig<CM, SSB> {
    CompilerConfig {
        cell_manager,
        step_selector_builder,
    }
}

pub fn compile<F: Field + Hash + Clone, CM: CellManager, SSB: StepSelectorBuilder, TraceArgs>(
    config: CompilerConfig<CM, SSB>,
    ast: &astCircuit<F, TraceArgs>,
) -> (Circuit<F>, Option<AssignmentGenerator<F, TraceArgs>>) {
    let mut unit = CompilationUnit::from(ast);

    config.cell_manager.place(&mut unit);

    compile_exposed(ast, &mut unit);

    compile_constraints(ast, &mut unit);

    config.step_selector_builder.build::<F>(&mut unit);

    let assignment = ast.trace.as_ref().map(|v| {
        AssignmentGenerator::new(
            unit.uuid,
            unit.placement.clone(),
            unit.selector.clone(),
            unit.matrix_values.clone(),
            TraceGenerator::new(Rc::clone(v), ast.num_steps),
            AutoTraceGenerator::from(ast),
        )
    });

    (unit.into(), assignment)
}

fn compile_exposed<F, TraceArgs>(ast: &astCircuit<F, TraceArgs>, unit: &mut CompilationUnit<F>) {
    for (queriable, offset) in &ast.exposed {
        let exposed = match queriable {
            Queriable::Forward(forward_signal, _) => {
                let step = match offset {
                    ExposeOffset::First => 0,
                    ExposeOffset::Last => unit.num_steps - 1,
                    ExposeOffset::Step(step) => *step,
                };
                (
                    step,
                    SignalPlacement::new(
                        forward_signal.uuid(),
                        forward_signal.annotation(),
                        unit.placement.forward(forward_signal.uuid()).offset(),
                    ),
                )
            }
            Queriable::Shared(shared_signal, _) => {
                let step = match offset {
                    ExposeOffset::First => 0,
                    ExposeOffset::Last => unit.num_steps - 1,
                    ExposeOffset::Step(step) => *step,
                };
                (
                    step,
                    SignalPlacement::new(
                        shared_signal.uuid(),
                        shared_signal.annotation(),
                        unit.placement.forward.len() as u32
                            + unit.placement.forward(shared_signal.uuid()).offset(),
                    ),
                )
            }
            _ => panic!("Queriable was not Forward or Shared"),
        };
        unit.exposed.push(exposed);
    }
}

fn compile_constraints<F: Field + Clone, TraceArgs>(
    _: &astCircuit<F, TraceArgs>,
    unit: &mut CompilationUnit<F>,
) {
    for step in unit.step_types.clone().values() {
        let step_annotation = unit
            .annotations
            .get(&step.uuid())
            .unwrap_or(&"??".to_string())
            .to_owned();

        let mut polys = Vec::new();
        for constr in step.constraints.iter() {
            let poly = transform_expr(unit, step, &constr.expr.clone());
            polys.push(Poly {
                expr: poly,
                step_uuid: step.uuid(),
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        for constr in step.transition_constraints.iter() {
            let poly = transform_expr(unit, step, &constr.expr.clone());
            polys.push(Poly {
                expr: poly,
                step_uuid: step.uuid(),
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        unit.polys.insert(step.uuid(), polys);
    }
}

fn transform_expr<F: Clone>(
    unit: &CompilationUnit<F>,
    step: &StepType<F>,
    source: &PIR<F>,
) -> PolyExpr<F> {
    match source.clone() {
        Expr::Const(c) => PolyExpr::Const(c),
        Expr::Query(q) => place_queriable(unit, step, q),
        Expr::Sum(v) => PolyExpr::Sum(
            v.into_iter()
                .map(|e| transform_expr(unit, step, &e))
                .collect(),
        ),
        Expr::Mul(v) => PolyExpr::Mul(
            v.into_iter()
                .map(|e| transform_expr(unit, step, &e))
                .collect(),
        ),
        Expr::Neg(v) => PolyExpr::Neg(Box::new(transform_expr(unit, step, &v))),
        Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(transform_expr(unit, step, &v)), exp),
        Expr::Halo2Expr(_) => panic!("halo2 expr not done"),
        Expr::MI(_) => panic!("mi elimination not done"),
    }
}

fn place_queriable<F: Clone>(
    unit: &CompilationUnit<F>,
    step: &StepType<F>,
    q: Queriable<F>,
) -> PolyExpr<F> {
    match q {
        // (UUID, UUID, String, u32)
        Queriable::Forward(forward, next) => {
            let annotation = if let Some(annotation) = unit.annotations.get(&forward.uuid()) {
                if next {
                    format!("forward next({})", annotation)
                } else {
                    format!("forward {}", annotation)
                }
            } else {
                "forward".to_string()
            };
            PolyExpr::Query((forward.uuid(), step.uuid(), annotation, next))
        }
        Queriable::Shared(shared, rot) => {
            let annotation = if let Some(annotation) = unit.annotations.get(&shared.uuid()) {
                if rot == 0 {
                    format!("shared({})", annotation)
                } else {
                    format!("shared_rot_{}({})", rot, annotation)
                }
            } else {
                "forward".to_string()
            };
            PolyExpr::Query((shared.uuid(), step.uuid(), annotation, false))
        }
        Queriable::Fixed(fixed, rot) => {
            let annotation = if let Some(annotation) = unit.annotations.get(&fixed.uuid()) {
                if rot == 0 {
                    format!("fixed({})", annotation)
                } else {
                    format!("fixed_rot_{}({})", rot, annotation)
                }
            } else {
                "fixed".to_string()
            };
            PolyExpr::Query((fixed.uuid(), step.uuid(), annotation, false))
        }
        Queriable::Internal(signal) => {
            let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                format!("internal {}", annotation)
            } else {
                "internal".to_string()
            };

            PolyExpr::Query((signal.uuid(), step.uuid(), annotation, false))
        }

        Queriable::StepTypeNext(_) => panic!("jarrl"),
        Queriable::Halo2AdviceQuery(..) => panic!("jarrl"),
        Queriable::Halo2FixedQuery(..) => panic!("jarrl"),
        Queriable::_unaccessible(_) => panic!("jarrl"),
    }
}
