pub mod cell_manager;
pub mod step_selector;
pub(crate) mod unit;

use std::{collections::HashMap, hash::Hash, rc::Rc};
use unit::CompilationUnit;

use crate::{
    ccs::ir::{assignments::AssignmentGenerator, circuit::Circuit, CoeffsForSteps, Poly, PolyExpr},
    field::Field,
    poly::Expr,
    sbpir::{query::Queriable, ExposeOffset, PIR, SBPIR as astCircuit},
    util::{uuid, UUID},
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

    compile_matrix_coeffs(&mut unit);

    config.step_selector_builder.build::<F>(&mut unit);

    let assignment = ast.trace.as_ref().map(|v| {
        AssignmentGenerator::new(
            unit.uuid,
            unit.placement.clone(),
            unit.selector.clone(),
            unit.matrix_coeffs.clone(),
            TraceGenerator::new(Rc::clone(v), ast.num_steps),
            AutoTraceGenerator::from(ast),
        )
    });

    (unit.into(), assignment)
}

fn compile_exposed<F, TraceArgs>(ast: &astCircuit<F, TraceArgs>, unit: &mut CompilationUnit<F>) {
    for (queriable, offset) in &ast.exposed {
        let step_idx = match offset {
            ExposeOffset::First => 0,
            ExposeOffset::Last => unit.num_steps - 1,
            ExposeOffset::Step(step) => *step,
        };
        let signal = match queriable {
            Queriable::Forward(forward_signal, _) => SignalPlacement::new(
                forward_signal.uuid(),
                "exposed:".to_owned() + &forward_signal.annotation(),
            ),
            Queriable::Shared(shared_signal, _) => SignalPlacement::new(
                shared_signal.uuid(),
                "exposed:".to_owned() + &shared_signal.annotation(),
            ),
            _ => panic!("Queriable was not Forward or Shared"),
        };
        unit.exposed.push((step_idx, signal));
    }
}

fn compile_constraints<F: Field + Clone, TraceArgs>(
    ast: &astCircuit<F, TraceArgs>,
    unit: &mut CompilationUnit<F>,
) {
    for step in ast.step_types.clone().values() {
        let step_annotation = unit
            .annotations
            .get(&step.uuid())
            .unwrap_or(&"??".to_string())
            .to_owned();

        let mut polys = Vec::new();
        for constr in step.constraints.iter() {
            let poly = transform_expr(step.uuid(), &unit.annotations, &constr.expr.clone());
            polys.push(Poly {
                uuid: uuid(),
                step_uuid: step.uuid(),
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
                expr: poly,
            })
        }

        for constr in step.transition_constraints.iter() {
            let poly = transform_expr(step.uuid(), &unit.annotations, &constr.expr.clone());
            polys.push(Poly {
                uuid: uuid(),
                step_uuid: step.uuid(),
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
                expr: poly,
            })
        }

        unit.polys.insert(step.uuid(), polys);
    }
}

fn transform_expr<F: Clone>(
    step_id: UUID,
    annotations: &HashMap<UUID, String>,
    source: &PIR<F>,
) -> PolyExpr<F> {
    match source.clone() {
        Expr::Const(c) => PolyExpr::Const(c),
        Expr::Query(q) => place_queriable(step_id, annotations, q),
        Expr::Sum(v) => PolyExpr::Sum(
            v.into_iter()
                .map(|e| transform_expr(step_id, annotations, &e))
                .collect(),
        ),
        Expr::Mul(v) => PolyExpr::Mul(
            v.into_iter()
                .map(|e| transform_expr(step_id, annotations, &e))
                .collect(),
        ),
        Expr::Neg(v) => PolyExpr::Neg(Box::new(transform_expr(step_id, annotations, &v))),
        Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(transform_expr(step_id, annotations, &v)), exp),
        Expr::Halo2Expr(_) => panic!("halo2 expr not done"),
        Expr::MI(_) => panic!("mi elimination not done"),
    }
}

fn place_queriable<F: Clone>(
    step_id: UUID,
    annotations: &HashMap<UUID, String>,
    q: Queriable<F>,
) -> PolyExpr<F> {
    match q {
        // (UUID, UUID, String, u32)
        Queriable::Forward(forward, next) => {
            let annotation = if let Some(annotation) = annotations.get(&forward.uuid()) {
                if next {
                    format!("forward next({})", annotation)
                } else {
                    format!("forward {}", annotation)
                }
            } else {
                "forward".to_string()
            };
            PolyExpr::Query((forward.uuid(), step_id, annotation, next))
        }
        Queriable::Shared(shared, rot) => {
            let annotation = if let Some(annotation) = annotations.get(&shared.uuid()) {
                if rot == 0 {
                    format!("shared({})", annotation)
                } else {
                    format!("shared_rot_{}({})", rot, annotation)
                }
            } else {
                "forward".to_string()
            };
            PolyExpr::Query((shared.uuid(), step_id, annotation, false))
        }
        Queriable::Fixed(fixed, rot) => {
            let annotation = if let Some(annotation) = annotations.get(&fixed.uuid()) {
                if rot == 0 {
                    format!("fixed({})", annotation)
                } else {
                    format!("fixed_rot_{}({})", rot, annotation)
                }
            } else {
                "fixed".to_string()
            };
            PolyExpr::Query((fixed.uuid(), step_id, annotation, false))
        }
        Queriable::Internal(signal) => {
            let annotation = if let Some(annotation) = annotations.get(&signal.uuid()) {
                format!("internal {}", annotation)
            } else {
                "internal".to_string()
            };

            PolyExpr::Query((signal.uuid(), step_id, annotation, false))
        }

        Queriable::StepTypeNext(_) => panic!("jarrl"),
        Queriable::Halo2AdviceQuery(..) => panic!("jarrl"),
        Queriable::Halo2FixedQuery(..) => panic!("jarrl"),
        Queriable::_unaccessible(_) => panic!("jarrl"),
    }
}

fn compile_matrix_coeffs<F: Field>(unit: &mut CompilationUnit<F>) {
    let mut coeffs: CoeffsForSteps<F> = HashMap::new();
    for (step_id, polys) in unit.polys.iter() {
        // one step
        let coeffs_one_step = polys
            .iter()
            .map(|poly| {
                // one poly
                poly.expr.poly_to_coeffs(true)
            })
            .collect();
        coeffs.insert(*step_id, coeffs_one_step);
    }
    unit.matrix_coeffs = coeffs;
}
