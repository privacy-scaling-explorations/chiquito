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
        Expression::Call(_, _, args) => {
            args.iter().for_each(|arg| undeclared_rule(analyser, arg));
        }
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

// Cannot transition to a non-existing state.
fn state_rule(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    if let Statement::Transition(_, state, _) = expr {
        // State "final" is implicit and may not always be present in the code.
        if state.name() == "final" {
            return;
        }
        let found_symbol = &analyser
            .symbols
            .find_symbol(&analyser.cur_scope, state.name());

        if found_symbol.is_none()
            || found_symbol.as_ref().unwrap().symbol.category != SymbolCategory::State
        {
            analyser.error(
                format!("Cannot transition to non-existing state `{}`", state.name()),
                &expr.get_dsym(),
            );
        }
    }
}

// Should only allow to assign `<--` or assign and assert `<==` signals (and not wg vars).
// Left hand side should only have signals.
fn assignment_rule(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    let (ids, rhs) = match expr {
        Statement::SignalAssignment(_, id, rhs) => (id, rhs),
        Statement::SignalAssignmentAssert(_, id, rhs) => (id, rhs),
        _ => return,
    };

    if let Expression::Call(_, machine, _) = &rhs[0] {
        let machine_scope = vec!["/".to_string(), machine.name()];
        let found_machine = &analyser.symbols.find_symbol(&machine_scope, machine.name());

        if found_machine.is_some()
            && found_machine.as_ref().unwrap().symbol.category == SymbolCategory::Machine
        {
            let outs = &found_machine.as_ref().unwrap().symbol.outs;
            if outs.is_some() {
                let outs = &outs.clone().unwrap();
                if outs.len() != ids.len() {
                    analyser.error(
                                format!(
                                    "Machine `{}` has {} output(s), but left hand side has {} identifier(s)",
                                    machine.name(),
                                    outs.len(),
                                    ids.len()
                                ),
                                &machine.debug_sym_ref(),
                            )
                }
            }
        }
    } else if ids.len() != rhs.len() {
        analyser.error(
            format!(
                "Left hand side has {} identifier(s), but right hand side has {} expression(s)",
                ids.len(),
                rhs.len()
            ),
            &expr.get_dsym(),
        )
    }

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
    if analyser
        .symbols
        .find_symbol(&analyser.cur_scope, id.name())
        .is_some()
    {
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

// Cannot use true or false if it's not inside of a logic expression.
fn true_false_rule(analyser: &mut Analyser, expr: &Expression<BigInt, Identifier>) {
    use Expression::*;

    match expr {
        BinOp { lhs, rhs, .. } => {
            check_true_false(analyser, expr, lhs);
            check_true_false(analyser, expr, rhs);
            true_false_rule(analyser, lhs);
            true_false_rule(analyser, rhs);
        }
        UnaryOp { sub, .. } => {
            check_true_false(analyser, expr, sub);
            true_false_rule(analyser, sub);
        }
        Select {
            cond,
            when_true,
            when_false,
            ..
        } => {
            check_true_false(analyser, expr, cond);
            check_true_false(analyser, expr, when_true);
            check_true_false(analyser, expr, when_false);
            true_false_rule(analyser, cond);
            true_false_rule(analyser, when_true);
            true_false_rule(analyser, when_false);
        }
        _ => (),
    }
}

fn check_true_false(
    analyser: &mut Analyser,
    expr: &Expression<BigInt, Identifier>,
    sub_expr: &Expression<BigInt, Identifier>,
) {
    if !expr.is_logic() {
        if let Expression::True(dsym) = sub_expr {
            analyser.error(format!("Cannot use true in expression {:#?}", expr), dsym)
        } else if let Expression::False(dsym) = sub_expr {
            analyser.error(format!("Cannot use false in expression {:#?}", expr), dsym)
        }
    }
}

// Can only declare field and bool for every signal and var.
fn types_rule(
    analyser: &mut Analyser,
    expr: &Statement<BigInt, Identifier>,
    id: &Identifier,
    symbol: &SymTableEntry,
) {
    if symbol.get_type() != "field" && symbol.get_type() != "bool" {
        analyser.error(
            format!(
                "Cannot declare {} with type {}, only field and bool are allowed.",
                id.name(),
                symbol.get_type()
            ),
            &expr.get_dsym(),
        )
    }
}

fn types_rule_tl(
    analyser: &mut Analyser,
    decl: &TLDecl<BigInt, Identifier>,
    id: &Identifier,
    symbol: &SymTableEntry,
) {
    if symbol.get_type() != "field" && symbol.get_type() != "bool" {
        analyser.error(
            format!(
                "Cannot declare {} with type {}, only field and bool are allowed.",
                id.name(),
                symbol.get_type()
            ),
            &decl.get_dsym(),
        )
    }
}

/// Check if the condition in an if statement is a logic expression (allowing bool literals and
/// signals).
fn if_condition_rule(analyser: &mut Analyser, stmt: &Statement<BigInt, Identifier>) {
    match stmt {
        Statement::IfThen(dsym, cond, _) | Statement::IfThenElse(dsym, cond, _, _) => {
            // Check if the condition is a logic expression
            let cond = cond.as_ref();
            match cond {
                Expression::True(_) | Expression::False(_) => {}

                // Check if the signal is a bool
                Expression::Query(_, s) => {
                    if let Some(symbol) =
                        analyser.symbols.find_symbol(&analyser.cur_scope, s.name())
                    {
                        if symbol.symbol.get_type() != "bool" {
                            analyser.error(
                                format!(
                                    "Signal {:#?} in if statement condition must be bool",
                                    cond
                                ),
                                dsym,
                            )
                        }
                    }
                }
                _ => {
                    if !cond.is_logic() {
                        analyser.error(
                            format!(
                                "Condition {:#?} in if statement must be a logic expression",
                                cond
                            ),
                            dsym,
                        )
                    }
                }
            }
        }
        _ => {}
    }
}

// Left side of "=" should be only wg vars, no signals.
fn wg_assignment_rule(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    let ids = match expr {
        Statement::WGAssignment(_, id, _) => id,
        _ => return,
    };

    ids.iter().for_each(|id| {
        if let Some(symbol) = analyser.symbols.find_symbol(&analyser.cur_scope, id.name()) {
            let is_wgvar = matches!(
                symbol.symbol.category,
                SymbolCategory::WGVar
                    | SymbolCategory::InputWGVar
                    | SymbolCategory::OutputWGVar
                    | SymbolCategory::InoutWGVar
            );
            if !is_wgvar {
                analyser.error(
                    format!(
                        "Cannot assign with = to {:#?} {}, you can only assign to WGVars. Use <-- or <== instead.",
                        symbol.symbol.category,
                        id.name()
                    ),
                    &expr.get_dsym(),
                )
            }
        }
    });
}

fn hyper_transition_rule(analyser: &mut Analyser, expr: &Statement<BigInt, Identifier>) {
    if let Statement::HyperTransition(_, assign_call, _) = expr {
        match *assign_call.to_owned() {
            Statement::SignalAssignmentAssert(_, ids, _) => {
                ids.iter().for_each(|id| {
        if id.1 != 1 {
            analyser.error(
                format!(
                    "All assigned identifiers in the hyper-transition must have a forward rotation ('), but `{}` is missing it.",
                    id.name(),
                ),
                &id.debug_sym_ref(),
            )
        }
    });
            }
            _ => analyser.error(
                "Hyper transition must include an assignment with assertion (<==).".to_string(),
                &expr.get_dsym(),
            ),
        }
    }
    if let Statement::Block(_, stmts) = expr {
        // There can only be a hyper-transition after a hyper-transition in a block
        stmts.iter().enumerate().for_each(|(idx, stmt)| {
            if idx < stmts.len() - 1
                && let Statement::HyperTransition(_, _, _) = stmt
            {
                let next_stmt = &stmts[idx + 1];
                analyser.error(
                    "Hyper-transition should be the last statement in a block".to_string(),
                    &next_stmt.get_dsym(),
                )
            }
        });
    }
}

fn call_rules(analyser: &mut Analyser, expr: &Expression<BigInt, Identifier>) {
    if let Expression::Call(_, machine, exprs) = expr {
        // Argument expressions in a call statement should not have nonzero rotation.
        exprs
            .iter()
            .for_each(|expr| detect_nonzero_rotation(expr, analyser));

        let machine_scope = vec!["/".to_string(), machine.name()];
        let found_machine = &analyser.symbols.find_symbol(&machine_scope, machine.name());
        if found_machine.is_none()
            || found_machine.as_ref().unwrap().symbol.category != SymbolCategory::Machine
        {
            analyser.error(
                format!(
                    "Call statement must call a valid machine, but `{}` is not a machine.",
                    machine.name()
                ),
                &machine.debug_sym_ref(),
            )
        } else if found_machine.as_ref().unwrap().symbol.category == SymbolCategory::Machine {
            let ins = &found_machine.as_ref().unwrap().symbol.ins;
            if ins.is_some() {
                let ins = &ins.clone().unwrap();
                if ins.len() != exprs.len() {
                    analyser.error(
                        format!(
                            "Expected {} argument(s) for `{}`, but got {}.",
                            ins.len(),
                            machine.name(),
                            exprs.len()
                        ),
                        &machine.debug_sym_ref(),
                    )
                }
                for (input, arg) in ins.iter().zip(exprs.iter()) {
                    let input = analyser
                        .symbols
                        .find_symbol(&machine_scope, input.to_string());
                    if input.is_none() {
                        unreachable!("Machine input should be added to the symbol table")
                    } else {
                        let input = input.unwrap();
                        let arg_is_signal = is_signal_recursive(analyser, arg);
                        if input.symbol.is_signal() != arg_is_signal {
                            analyser.error(
                                format!(
                                    "Cannot assign {} `{:?}` to input {} `{}`",
                                    if arg_is_signal { "signal" } else { "variable" },
                                    arg,
                                    if input.symbol.is_signal() {
                                        "signal"
                                    } else {
                                        "variable"
                                    },
                                    input.symbol.id,
                                ),
                                expr.get_dsym(),
                            )
                        }
                    }
                }
            }
        }

        let mut current_machine_scope = analyser.cur_scope.clone();
        current_machine_scope.truncate(2);
        if machine_scope == *current_machine_scope {
            analyser.error(
                "A machine should not call itself.".to_string(),
                &machine.debug_sym_ref(),
            )
        }
    }
}

/// Check if the expression result is a signal. For each of the Queries in the expression, check if
/// the identifier is a signal.
fn is_signal_recursive(analyser: &Analyser, expr: &Expression<BigInt, Identifier>) -> bool {
    let mut is_signal = true;
    match expr {
        Expression::Query(_, id) => {
            if let Some(symbol) = analyser.symbols.find_symbol(&analyser.cur_scope, id.name()) {
                is_signal = is_signal && symbol.symbol.is_signal();
            }
        }
        Expression::BinOp { lhs, rhs, .. } => {
            is_signal = is_signal
                && is_signal_recursive(analyser, lhs)
                && is_signal_recursive(analyser, rhs);
        }
        Expression::UnaryOp { sub, .. } => {
            is_signal = is_signal && is_signal_recursive(analyser, sub);
        }
        Expression::Select {
            cond,
            when_true,
            when_false,
            ..
        } => {
            is_signal = is_signal
                && is_signal_recursive(analyser, cond)
                && is_signal_recursive(analyser, when_true)
                && is_signal_recursive(analyser, when_false);
        }
        _ => (),
    }
    is_signal
}

fn detect_nonzero_rotation(expr: &Expression<BigInt, Identifier>, analyser: &mut Analyser) {
    match expr {
        Expression::Query(_, id) => {
            if id.1 != 0 {
                analyser.error(
                    "Non-zero rotation is not allowed in a call.".to_string(),
                    &id.debug_sym_ref(),
                )
            }
        }
        Expression::BinOp {
            dsym: _,
            op: _,
            lhs,
            rhs,
        } => {
            detect_nonzero_rotation(lhs, analyser);
            detect_nonzero_rotation(rhs, analyser);
        }
        Expression::UnaryOp {
            dsym: _,
            op: _,
            sub,
        } => {
            detect_nonzero_rotation(sub, analyser);
        }
        Expression::Select {
            dsym: _,
            cond,
            when_true,
            when_false,
        } => {
            detect_nonzero_rotation(cond, analyser);
            detect_nonzero_rotation(when_true, analyser);
            detect_nonzero_rotation(when_false, analyser);
        }
        _ => (),
    }
}

lazy_static! {
    /// Global semantic analyser rules.
    pub(super) static ref RULES: RuleSet = RuleSet {
        expression: vec![undeclared_rule, true_false_rule,  call_rules],
        statement: vec![state_decl, assignment_rule, assert_rule, if_condition_rule, wg_assignment_rule, state_rule, hyper_transition_rule],
        new_symbol: vec![rotation_decl, redeclare_rule, types_rule],
        new_tl_symbol: vec![rotation_decl_tl, machine_decl_tl, types_rule_tl],
    };
}

#[cfg(test)]
mod test {
    use crate::{
        compiler::semantic::analyser::analyse,
        parser::{ast::debug_sym_factory::DebugSymRefFactory, lang},
    };

    #[test]
    fn test_analyser_undeclared() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal i; // a is undeclared

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
           }
        ",
            r#"[SemErr { msg: "use of undeclared variable a", dsym: nofile:18:20 }]"#,
        )
    }

    #[test]
    fn test_analyser_rotation_decl() {
        do_test(
            "
        machine fibo'(signal n) (signal b: field) {
            signal a, i;
            
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
           }
        ",
            r#"[SemErr { msg: "There cannot be rotation in identifier declaration of fibo", dsym: nofile:2:9 }]"#,
        );

        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a, i;
            
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
           }
        ",
            r#"[SemErr { msg: "There cannot be rotation in identifier declaration of initial", dsym: nofile:5:13 }]"#,
        );

        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a, i;
            
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
           }
        ",
            r#"[SemErr { msg: "There cannot be rotation in identifier declaration of c", dsym: nofile:6:14 }]"#,
        )
    }

    #[test]
    fn test_analyser_state_decl() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a, i;
            
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
           }
        ",
            r#"[SemErr { msg: "Cannot declare state nested here", dsym: nofile:8:17 }]"#,
        );

        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a, i;
            
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
           }
        ",
            r#"[SemErr { msg: "Cannot declare state nested here", dsym: nofile:13:15 }]"#,
        );
    }

    #[test]
    fn test_assignment_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
            
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
           }
        ",
            r#"[SemErr { msg: "Cannot assign with <-- or <== to variable wrong with category WGVar, you can only assign to signals. Use = instead.", dsym: nofile:9:14 }]"#,
        );
    }

    #[test]
    fn test_assert_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
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
           }
        ",
            r#"[SemErr { msg: "Cannot use wgvar wrong in statement assert wrong == 3;", dsym: nofile:18:14 }, SemErr { msg: "Cannot use wgvar wrong in statement [c] <== [(a + b) + wrong];", dsym: nofile:20:14 }]"#,
        )
    }

    #[test]
    fn test_machine_decl_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;

            i, a, b, c <== 1, 1, 1, 2; // this cannot be here

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
           }
        ",
            r#"[SemErr { msg: "Cannot declare [i, a, b, c] <== [1, 1, 1, 2]; in the machine, only states, wgvars and signals are allowed", dsym: nofile:2:9 }, SemErr { msg: "Cannot declare if (i + 1) == n { [a] <-- [3]; } else { [b] <== [3]; } in the machine, only states, wgvars and signals are allowed", dsym: nofile:2:9 }]"#,
        );
    }

    #[test]
    fn test_redeclare_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
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
           }
        ",
            r#"[SemErr { msg: "Cannot redeclare middle in the same scope [\"/\", \"fibo\"]", dsym: nofile:22:13 }, SemErr { msg: "Cannot redeclare n in the same scope [\"/\", \"fibo\"]", dsym: nofile:14:13 }, SemErr { msg: "Cannot redeclare c in the same scope [\"/\", \"fibo\", \"middle\"]", dsym: nofile:24:14 }]"#,
        );
    }

    #[test]
    fn test_types_rule() {
        do_test(
            "
        machine fibo(signal n: uint) (signal b: field) {
            signal a: field, i;
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c: int; // wrong type

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
           }
        ",
            r#"[SemErr { msg: "Cannot declare n with type uint, only field and bool are allowed.", dsym: nofile:2:22 }, SemErr { msg: "Cannot declare c with type int, only field and bool are allowed.", dsym: nofile:15:14 }]"#,
        );
    }

    #[test]
    fn test_true_false_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
            state initial {
             signal c;
             var is_true;
             is_true = true;

             i, a, b, c <== 1, 1, 1, 2 + true; // wrong

             if false {
                a <== 1;
             }

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == 0 {
                if 1 * true ^ false - 123 && 0 + false * false == 0 {
                    a <== 1;
                }
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }
           }
        ",
            r#"[SemErr { msg: "Cannot use true in expression 2 + true", dsym: nofile:9:42 }, SemErr { msg: "Cannot use true in expression 1 * true", dsym: nofile:26:24 }, SemErr { msg: "Cannot use false in expression false - 123", dsym: nofile:26:31 }, SemErr { msg: "Cannot use false in expression false * false", dsym: nofile:26:50 }, SemErr { msg: "Cannot use false in expression false * false", dsym: nofile:26:58 }]"#,
        );
    }

    #[test]
    fn test_if_expression_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             if false {                 // allowed
                a <== 1;
             }

             if 3 + i == a {            // allowed
                a <== 1;
             }

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;
             signal t: bool;

             c <== a + b;

             t <== true;

             if i + 1 {                 // wrong
                if c {                  // wrong
                    a <== 1;
                }
                if t {                  // allowed
                    a <== 1;
                }
                if 4 {                  // wrong
                    a <== 1;
                }
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }
           }
        ",
            r#"[SemErr { msg: "Condition i + 1 in if statement must be a logic expression", dsym: nofile:30:14 }, SemErr { msg: "Signal c in if statement condition must be bool", dsym: nofile:31:17 }, SemErr { msg: "Condition 4 in if statement must be a logic expression", dsym: nofile:37:17 }]"#,
        );
    }

    #[test]
    fn test_wg_assignment_rule() {
        do_test(
            "
        machine fibo(signal n) (signal b: field) {
            signal a: field, i;
            var wgvar;
            state initial {
             signal c;

             wgvar = 31;
             i = 0;                      // wrong

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
           }
        ",
            r#"[SemErr { msg: "Cannot assign with = to Signal i, you can only assign to WGVars. Use <-- or <== instead.", dsym: nofile:9:14 }]"#,
        );
    }

    #[test]
    fn test_assignment_args_count() {
        // The number of identifiers and expressions in the assignment should be equal:
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e: field;
            state initial {
                c' <-- d, e;
            }
        }
        ",
            r#"[SemErr { msg: "Left hand side has 1 identifier(s), but right hand side has 2 expression(s)", dsym: nofile:6:17 }]"#,
        );

        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e: field;
            state initial {
                c' <== d, e;
            }
        }
        ",
            r#"[SemErr { msg: "Left hand side has 1 identifier(s), but right hand side has 2 expression(s)", dsym: nofile:6:17 }]"#,
        );
    }

    #[test]
    fn test_transition_to_valid_state() {
        // The transition should be to a valid state. Trying to transition to a state that does not
        // exist:
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            state initial {
                -> no_state;
            }
        }
        ",
            r#"[SemErr { msg: "Cannot transition to non-existing state `no_state`", dsym: nofile:4:17 }]"#,
        );
    }

    #[test]
    fn test_call_assignments_rotation() {
        // Testing the mandatory identifier rotation syntax
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            state initial {
                b <== other(n) -> final;
            }
        }
        machine other (signal n) (signal b: field) {
            state initial {
                b' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "All assigned identifiers in the hyper-transition must have a forward rotation ('), but `b` is missing it.", dsym: nofile:4:17 }]"#,
        );
    }

    #[test]
    fn test_call_no_expression_rotation() {
        // Testing the absence of rotation in expressions
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e;
            state initial {
                c' <== other(d + e') -> final;
            }
        }
        machine other (signal n) (signal b: field) {
            state initial {
                b' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "Non-zero rotation is not allowed in a call.", dsym: nofile:6:34 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_valid_machine() {
        // The callee should be a valid machine. Trying to call a machine that does not exist:
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e;
            state initial {
                c' <== other(d + e) -> final;
            }
        }
        ",
            r#"[SemErr { msg: "Call statement must call a valid machine, but `other` is not a machine.", dsym: nofile:6:24 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_call_itself() {
        // The callee should be a valid machine. Trying to call itself:
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e;
            state initial {
                c' <== caller(d + e) -> final;
            }
        }
        ",
            r#"[SemErr { msg: "A machine should not call itself.", dsym: nofile:6:24 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_valid_state() {
        // The transition should be to a valid state. Trying to transition to a state that does not
        // exist:
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e;
            state initial {
                c' <== other(d + e) -> no_state;
            }
        }
        machine other (signal n) (signal b: field) {
            state initial {
                b' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "Cannot transition to non-existing state `no_state`", dsym: nofile:6:37 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_is_the_last() {
        // The hyper-transition should be the last statement in a block
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e;
            state initial {
                c' <== other(d + e) -> final;
                c' <== 1;
            }
        }
        machine other (signal n) (signal b: field) {
            state initial {
                b' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "Hyper-transition should be the last statement in a block", dsym: nofile:7:17 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_call_arg_count() {
        // Cannot call a machine with the wrong number of arguments
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            signal d, e: field;
            state initial {
                c' <== other(d, e) -> final;
            }
        }
        machine other (signal n) (signal b: field) {
            state initial {
                b' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "Expected 1 argument(s) for `other`, but got 2.", dsym: nofile:6:24 }]"#,
        );
    }

    #[test]
    fn test_hyper_transition_assignment_arg_count() {
        // Cannot assign call result with the wrong number of arguments
        do_test(
            "
        machine caller (signal n) (signal b: field) {
            signal c;
            state initial {
                c' <== other(n) -> final;
            }
        }
        machine other (signal n) (signal b: field, signal c: field) {
            state initial {
                b' <== n;
                c' <== n;
            }
        }
        ",
            r#"[SemErr { msg: "Machine `other` has 2 output(s), but left hand side has 1 identifier(s)", dsym: nofile:5:24 }]"#,
        );
    }

    fn do_test(circuit: &str, expected: &str) {
        let debug_sym_ref_factory = DebugSymRefFactory::new("", circuit);
        let decls = lang::TLDeclsParser::new()
            .parse(&debug_sym_ref_factory, circuit)
            .unwrap();
        let result = analyse(&decls);

        assert_eq!(format!("{:?}", result.messages), expected);
    }
}
