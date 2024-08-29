use std::collections::HashMap;

use itertools::Itertools;
use num_bigint::BigInt;

use crate::{
    field::Field,
    parser::ast::{
        statement::{Statement, TypedIdDecl},
        tl::TLDecl,
        DebugSymRef, Identifiable, Identifier,
    },
    poly::Expr,
};

use super::{abepi::CompilationUnit, semantic::SymTable};

pub(super) fn interpret(ast: &[TLDecl<BigInt, Identifier>], _symbols: &SymTable) -> Setup<BigInt> {
    let mut interpreter = SetupInterpreter {
        abepi: CompilationUnit::default(),
        setup: Setup::default(),
        current_machine: String::default(),
        current_state: String::default(),
    };

    interpreter.interpret(ast);

    interpreter.setup
}

/// Machine setup by machine name
pub(super) type Setup<F> = HashMap<String, MachineSetup<F>>;

pub(super) struct MachineSetup<F> {
    poly_constraints: HashMap<String, Vec<Expr<F, Identifier, DebugSymRef>>>,

    input_signals: Vec<TypedIdDecl<Identifier>>,
    output_signals: Vec<TypedIdDecl<Identifier>>,
}

impl<F> Default for MachineSetup<F> {
    fn default() -> Self {
        Self {
            poly_constraints: HashMap::new(),
            input_signals: vec![],
            output_signals: vec![],
        }
    }
}
impl MachineSetup<BigInt> {
    pub(crate) fn map_consts<F: Field>(&self) -> MachineSetup<F> {
        let poly_constraints: HashMap<String, Vec<Expr<F, Identifier, DebugSymRef>>> = self
            .poly_constraints_iter()
            .map(|(step_id, step)| {
                let new_step: Vec<Expr<F, Identifier, DebugSymRef>> = step
                    .iter()
                    .map(|pi| Self::convert_const_to_field(pi))
                    .collect();

                (step_id.clone(), new_step)
            })
            .collect();

        let new_machine: MachineSetup<F> = self.replace_poly_constraints(poly_constraints);
        new_machine
    }

    fn convert_const_to_field<F: Field>(
        expr: &Expr<BigInt, Identifier, DebugSymRef>,
    ) -> Expr<F, Identifier, DebugSymRef> {
        use Expr::*;
        match expr {
            Const(v, dsym) => Const(F::from_big_int(v), dsym.clone()),
            Sum(ses, dsym) => Sum(
                ses.iter()
                    .map(|se| Self::convert_const_to_field(se))
                    .collect(),
                dsym.clone(),
            ),
            Mul(ses, dsym) => Mul(
                ses.iter()
                    .map(|se| Self::convert_const_to_field(se))
                    .collect(),
                dsym.clone(),
            ),
            Neg(se, dsym) => Neg(Box::new(Self::convert_const_to_field(se)), dsym.clone()),
            Pow(se, exp, dsym) => Pow(
                Box::new(Self::convert_const_to_field(se)),
                *exp,
                dsym.clone(),
            ),
            Query(q, dsym) => Query(q.clone(), dsym.clone()),
            Halo2Expr(_, _) => todo!(),
            MI(se, dsym) => MI(Box::new(Self::convert_const_to_field(se)), dsym.clone()),
        }
    }
}

impl<F: Clone> MachineSetup<F> {
    fn new(
        inputs: Vec<Statement<BigInt, Identifier>>,
        outputs: Vec<Statement<BigInt, Identifier>>,
    ) -> Self {
        let mut created = Self::default();

        for input in inputs {
            if let Statement::SignalDecl(_, ids) = input {
                created.input_signals.extend(ids)
            }
        }

        for output in outputs {
            if let Statement::SignalDecl(_, ids) = output {
                created.output_signals.extend(ids)
            }
        }

        created
    }

    fn new_state<S: Into<String>>(&mut self, id: S) {
        self.poly_constraints.insert(id.into(), vec![]);
    }

    fn _has_state<S: Into<String>>(&self, id: S) -> bool {
        self.poly_constraints.contains_key(&id.into())
    }

    fn add_poly_constraints<S: Into<String>>(
        &mut self,
        state: S,
        poly_constraints: Vec<Expr<F, Identifier, DebugSymRef>>,
    ) {
        self.poly_constraints
            .get_mut(&state.into())
            .unwrap()
            .extend(poly_constraints);
    }

    pub(super) fn poly_constraints_iter(
        &self,
    ) -> std::collections::hash_map::Iter<String, Vec<Expr<F, Identifier, DebugSymRef>>> {
        self.poly_constraints.iter()
    }

    pub(super) fn replace_poly_constraints<F2>(
        &self,
        poly_constraints: HashMap<String, Vec<Expr<F2, Identifier, DebugSymRef>>>,
    ) -> MachineSetup<F2> {
        MachineSetup {
            poly_constraints,
            input_signals: self.input_signals.clone(),
            output_signals: self.output_signals.clone(),
        }
    }

    pub(super) fn states(&self) -> Vec<&String> {
        self.poly_constraints.keys().collect_vec()
    }

    pub(super) fn get_poly_constraints<S: Into<String>>(
        &self,
        state: S,
    ) -> Option<&Vec<Expr<F, Identifier, DebugSymRef>>> {
        self.poly_constraints.get(&state.into())
    }
}

struct SetupInterpreter {
    abepi: CompilationUnit<BigInt, Identifier>,

    /// Machine setup by machine name
    setup: Setup<BigInt>,

    current_machine: String,
    current_state: String,
}

impl SetupInterpreter {
    pub(super) fn interpret(&mut self, ast: &[TLDecl<BigInt, Identifier>]) {
        use TLDecl::*;
        ast.iter().for_each(|tl| match tl {
            MachineDecl {
                dsym,
                id,
                input_params,
                output_params,
                block,
            } => self.interpret_machine(dsym, id, input_params, output_params, block),
        });
    }

    fn interpret_machine(
        &mut self,
        _dsym: &DebugSymRef,
        id: &Identifier,
        input_params: &[Statement<BigInt, Identifier>],
        output_params: &[Statement<BigInt, Identifier>],
        block: &Statement<BigInt, Identifier>,
    ) {
        self.current_machine = id.name();
        self.setup.insert(
            id.name(),
            MachineSetup::new(input_params.to_owned(), output_params.to_owned()),
        );
        self.interpret_machine_statement(block);
    }

    fn interpret_machine_statement(&mut self, stmt: &Statement<BigInt, Identifier>) {
        match stmt {
            Statement::Block(_, block) => {
                block
                    .iter()
                    .for_each(|stmt| self.interpret_machine_statement(stmt));
            }
            Statement::StateDecl(dsym, id, stmt) => self.interpret_state_decl(dsym, id, stmt),
            Statement::SignalDecl(_, _) => {}
            Statement::WGVarDecl(_, _) => {}

            _ => unreachable!("semantic analyser should prevent this"),
        }
    }

    fn interpret_state_decl(
        &mut self,
        _dsym: &DebugSymRef,
        id: &Identifier,
        stmt: &Statement<BigInt, Identifier>,
    ) {
        self.current_state = id.name();
        self.setup
            .get_mut(&self.current_machine)
            .unwrap()
            .new_state(id.name());
        self.interpret_state_statement(stmt);
    }

    fn interpret_state_statement(&mut self, stmt: &Statement<BigInt, Identifier>) {
        use Statement::*;
        let result = match stmt {
            Block(_, block) => {
                block
                    .iter()
                    .for_each(|stmt| self.interpret_state_statement(stmt));
                vec![]
            }
            Assert(_, _)
            | SignalAssignmentAssert(_, _, _)
            | IfThen(_, _, _)
            | IfThenElse(_, _, _, _)
            | Transition(_, _, _) => self.abepi.compile_statement(stmt.clone()),

            StateDecl(_, _, _) => unreachable!("semantic analyser should prevent this"),

            SignalAssignment(_, _, _) | WGAssignment(_, _, _) => vec![],
            SignalDecl(_, _) | WGVarDecl(_, _) => vec![],
            HyperTransition(_, _, _, _) => todo!("Implement compilation for hyper transitions"),
        };

        self.add_poly_constraints(
            result
                .into_iter()
                .map(|cr| cr.anti_booly.transform_meta(|_| cr.dsym.clone()))
                .collect(),
        );
    }

    fn add_poly_constraints(&mut self, pis: Vec<Expr<BigInt, Identifier, DebugSymRef>>) {
        self.setup
            .get_mut(&self.current_machine)
            .unwrap()
            .add_poly_constraints(&self.current_state, pis);
    }
}
