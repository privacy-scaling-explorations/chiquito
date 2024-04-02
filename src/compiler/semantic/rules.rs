use std::vec;

use lazy_static::lazy_static;

use num_bigint::BigInt;

use crate::{
    compiler::semantic::{analyser::Analyser, RuleSet, SymTableEntry},
    parser::ast::{
        expression::Expression, statement::Statement, tl::TLDecl, DebugSymRef, Identifiable,
        Identifier,
    },
};

use super::SymbolCategory;

// Cannot use a undeclared variable in a expression.
fn undeclared_rule(analyser: &mut Analyser, expr: &Expression<BigInt, Identifier>) {
    match expr {
        Expression::Query(dsym, var) => {
            if analyser
                .symbols
                .find_symbol(&analyser.cur_scope, var.name())
                .is_none()
            {
                analyser.error(format!("use of undeclared variable {}", var.name()), dsym);
            }
        }

        Expression::BinOp { lhs, rhs, .. } => {
            undeclared_rule(analyser, lhs);
            undeclared_rule(analyser, rhs);
        }
        Expression::UnaryOp { sub, .. } => undeclared_rule(analyser, sub),
        Expression::Select {
            cond,
            when_true,
            when_false,
            ..
        } => {
            undeclared_rule(analyser, cond);
            undeclared_rule(analyser, when_true);
            undeclared_rule(analyser, when_false);
        }
        Expression::Const(_, _) | Expression::True(_) | Expression::False(_) => {}
    }
}

// Cannot declare identifiers with rotations. Rotation can only be used in expressions.
fn rotation_decl_tl(
    analyser: &mut Analyser,
    decl: &TLDecl<BigInt, Identifier>,
    id: &Identifier,
    _symbol: &SymTableEntry,
) {
    if id.rotation() != 0 {
        analyser.error(
            format!(
                "There cannot be rotation in identifier declaration of {}",
                id.name()
            ),
            &decl.get_dsym(),
        )
    }
}
fn rotation_decl(
    analyser: &mut Analyser,
    expr: &Statement<BigInt, Identifier>,
    id: &Identifier,
    _symbol: &SymTableEntry,
) {
    if id.rotation() != 0 {
        analyser.error(
            format!(
                "There cannot be rotation in identifier declaration of {}",
                id.name()
            ),
            &expr.get_dsym(),
        )
    }
}

// Cannot declare states in other block that is not the machine.
fn state_decl(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    let blocks = match expr {
        Statement::StateDecl(_, _, block) => vec![block],
        Statement::Transition(_, _, block) => vec![block],
        Statement::IfThen(_, _, block) => vec![block],
        Statement::IfThenElse(_, _, block, block_else) => vec![block, block_else],

        _ => vec![],
    };

    blocks.into_iter().for_each(|block| {
        if let Statement::Block(_, block) = *(block.clone()) {
            block.into_iter().for_each(|stmt| {
                if let Statement::StateDecl(dsym, id, _) = stmt {
                    analyser.error(format!("Cannot declare state {} here", id.name()), &dsym);
                }
            })
        } else {
            unreachable!("parser only generates blocks in this context");
        }
    });
}

// Should only allow to assign `<--` or assign and assert `<==` signals (and not wg vars).
// Left hand side should only have signals.
fn assignment_rule(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    let ids = match expr {
        Statement::SignalAssignment(_, id, _) => id,
        Statement::SignalAssignmentAssert(_, id, _) => id,
        _ => return,
    };

    ids.iter().for_each(|id| {
        if let Some(symbol) = analyser.symbols.find_symbol(&analyser.cur_scope, id.name()) {
            let is_signal = matches!(
                symbol.symbol.category,
                SymbolCategory::Signal | SymbolCategory::InputSignal | SymbolCategory::OutputSignal | SymbolCategory::InoutSignal
            );
            if !is_signal {
                analyser.error(
                    format!(
                        "Cannot assign with <-- or <== to variable {} with category {:#?}, you can only assign to signals. Use = instead.",
                        id.name(),
                        symbol.symbol.category
                    ),
                    &expr.get_dsym(),
                )
            }
        }
    });
}

// Cannot use wgvars in assert statements.
fn assert_rule(analyser: &mut Analyser, stmt: &Statement<BigInt, Identifier>) {
    let exprs = match stmt {
        Statement::SignalAssignmentAssert(_, _, exprs) => exprs.clone(),
        Statement::Assert(_, expr) => vec![expr.clone()],
        _ => return,
    };

    exprs.into_iter().for_each(|expr| {
        check_expr_for_wgvar(analyser, &expr, stmt, &stmt.get_dsym());
    });
}

// Helper function to check if an expression uses a wgvar recursively.
fn check_expr_for_wgvar(
    analyser: &mut Analyser,
    expr: &Expression<BigInt, Identifier>,
    stmt: &Statement<BigInt, Identifier>,
    dsym: &DebugSymRef,
) {
    use Expression::*;

    // Recursive
    match expr {
        BinOp { lhs, rhs, .. } => {
            check_expr_for_wgvar(analyser, lhs, stmt, dsym);
            check_expr_for_wgvar(analyser, rhs, stmt, dsym);
        }
        UnaryOp { sub, .. } => {
            check_expr_for_wgvar(analyser, sub, stmt, dsym);
        }
        Select {
            cond,
            when_true,
            when_false,
            ..
        } => {
            check_expr_for_wgvar(analyser, cond, stmt, dsym);
            check_expr_for_wgvar(analyser, when_true, stmt, dsym);
            check_expr_for_wgvar(analyser, when_false, stmt, dsym);
        }
        Query(_, id) => {
            if let Some(symbol) = analyser.symbols.find_symbol(&analyser.cur_scope, id.name()) {
                let is_wgvar = matches!(
                    symbol.symbol.category,
                    SymbolCategory::WGVar
                        | SymbolCategory::InputWGVar
                        | SymbolCategory::OutputWGVar
                        | SymbolCategory::InoutWGVar
                );
                if is_wgvar {
                    analyser.error(
                        format!("Cannot use wgvar {} in statement {:#?}", id.name(), stmt),
                        dsym,
                    )
                }
            }
        }
        _ => (), // For Const, True, False, do nothing
    }
}

// Cannot declare other than states, wgvars and signals in the machine.
fn machine_decl_tl(
    analyser: &mut Analyser,
    decl: &TLDecl<BigInt, Identifier>,
    _id: &Identifier,
    _symbol: &SymTableEntry,
) {
    match decl {
        TLDecl::MachineDecl { dsym, .. } => {
            let block = match decl {
                TLDecl::MachineDecl { block, .. } => block,
            };

            if let Statement::Block(_, block) = block {
                block.iter().for_each(|stmt| {
                    match stmt {
                        Statement::SignalDecl(_, _) => (),
                        Statement::WGVarDecl(_, _) => (),
                        Statement::StateDecl(..) => (),
                        _ => analyser.error(
                            format!(
                                "Cannot declare {:?} in the machine, only states, wgvars and signals are allowed",
                                stmt
                            ),
                            dsym,
                        ),
                        
                    }
                })
            } else {
                unreachable!("parser only generates blocks in this context");
            }
        }
        
    }
}

// Cannot redeclare a variable (wgvar, signal) or state in the same scope.
fn redeclare_rule(
    analyser: &mut Analyser,
    expr: &Statement<BigInt, Identifier>,
    id: &Identifier,
    _symbol: &SymTableEntry,
) {
    if analyser.symbols.find_symbol(&analyser.cur_scope, id.name()).is_some() {
        analyser.error(
            format!(
                "Cannot redeclare {} in the same scope {:?}",
                id.name(),
                analyser.cur_scope
            ),
            &expr.get_dsym(),
        )
    }
}

lazy_static! {
    /// Global semantic analyser rules.
    pub(super) static ref RULES: RuleSet = RuleSet {
        expression: vec![undeclared_rule],
        statement: vec![state_decl, assignment_rule, assert_rule],
        new_symbol: vec![rotation_decl, redeclare_rule],
        new_tl_symbol: vec![rotation_decl_tl, machine_decl_tl],
    };
}

#[cfg(test)]
mod test {
    use crate::{compiler::semantic::analyser::analyse, parser::lang};

    #[test]
    fn test_analyser_undeclared() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal i; // a is undeclared

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "use of undeclared variable a", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        )
    }

    #[test]
    fn test_analyser_rotation_decl() {
        let circuit = "
        machine fibo'(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "There cannot be rotation in identifier declaration of fibo", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );

        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial' {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "There cannot be rotation in identifier declaration of initial", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );

        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c';

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "There cannot be rotation in identifier declaration of c", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        )
    }

    #[test]
    fn test_analyser_state_decl() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

                state nested {
                    c <== 3;
                }

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot declare state nested here", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );

        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;

              state nested {
               c <== 3;
              }
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot declare state nested here", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );
    }

    #[test]
    fn test_assignment_rule() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;
             var wrong;

             i, a, b, wrong, c <== 1, 1, 1, 3, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot assign with <-- or <== to variable wrong with category WGVar, you can only assign to signals. Use = instead.", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );
    }

    #[test]
    fn test_assert_rule() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;
             var wrong;

             assert wrong == 3;

             c <== a + b + wrong;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot use wgvar wrong in statement assert wrong == 3;", dsym: DebugSymRef { start: 0, end: 0 } }, Err { msg: "Cannot use wgvar wrong in statement [c] <== [(a + b) + wrong];", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        )
    }

    #[test]
    fn test_machine_decl_rule() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            i, a, b, c <== 1, 1, 1, 2; // this cannot be here

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            if i + 1 == n { // this cannot be here
              a <-- 3;
            } else {
              b <== 3;
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot declare [i, a, b, c] <== [1, 1, 1, 2]; in the machine, only states, wgvars and signals are allowed", dsym: DebugSymRef { start: 0, end: 0 } }, Err { msg: "Cannot declare if (i + 1) == n { [a] <-- [3]; } else { [b] <== [3]; } in the machine, only states, wgvars and signals are allowed", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );
    }

    #[test]
    fn test_redeclare_rule() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            signal n; // cannot redeclare n

            state middle {
                -> final {
                    i', n' <== i + 1, n;
                }
            }

            state middle {
             signal c;
             signal c; // cannot redeclare c

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        let result = analyse(&decls);

        assert_eq!(
            format!("{:?}", result.messages),
            r#"[Err { msg: "Cannot redeclare middle in the same scope [\"/\", \"fibo\"]", dsym: DebugSymRef { start: 0, end: 0 } }, Err { msg: "Cannot redeclare n in the same scope [\"/\", \"fibo\"]", dsym: DebugSymRef { start: 0, end: 0 } }, Err { msg: "Cannot redeclare c in the same scope [\"/\", \"fibo\", \"middle\"]", dsym: DebugSymRef { start: 0, end: 0 } }]"#
        );
    }
}
