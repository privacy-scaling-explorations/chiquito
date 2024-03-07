use std::fmt::Debug;

use super::DebugSymRef;

#[derive(Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    // Arithmetic
    Sum,
    Sub,
    Mul,
    Pow,
    MulInv,
    Div,
    DivRem,

    // Logic
    Eq,
    NEq,
    Greater,
    Less,
    GreaterEq,
    LessEq,

    And,
    Or,
}

impl BinaryOperator {
    pub fn is_logic(&self) -> bool {
        use BinaryOperator::*;
        match self {
            Eq => true,
            NEq => true,
            And => true,
            Or => true,
            Greater => true,
            Less => true,
            GreaterEq => true,
            LessEq => true,
            Sum => false,
            _ => false,
        }
    }

    pub fn is_arith(&self) -> bool {
        !self.is_logic()
    }
}

impl Debug for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sum => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Pow => write!(f, "^"),
            Self::Div => write!(f, "/"),
            Self::DivRem => write!(f, "%"),
            Self::MulInv => write!(f, "\\"),
            Self::Eq => write!(f, "=="),
            Self::NEq => write!(f, "!="),
            Self::And => write!(f, "&&"),
            Self::Or => write!(f, "||"),
            Self::Greater => write!(f, ">"),
            Self::Less => write!(f, "<"),
            Self::GreaterEq => write!(f, ">="),
            Self::LessEq => write!(f, "<="),
        }
    }
}

impl From<String> for BinaryOperator {
    fn from(value: String) -> Self {
        use BinaryOperator::*;
        match value.as_str() {
            "+" => Sum,
            "-" => Sub,
            "*" => Mul,
            "^" => Pow,
            "/" => Div,
            "%" => DivRem,
            "\\" => MulInv,
            "==" => Eq,
            "!=" => NEq,
            ">" => Greater,
            "<" => Less,
            ">=" => GreaterEq,
            "<=" => LessEq,
            "&&" => Or,
            "||" => And,
            &_ => unreachable!(),
        }
    }
}

#[derive(Clone)]
pub enum UnaryOperator {
    Not,
    Neg,
}

impl UnaryOperator {
    pub fn is_logic(&self) -> bool {
        use UnaryOperator::*;
        match self {
            Not => true,
            Neg => false,
        }
    }

    pub fn is_arith(&self) -> bool {
        !self.is_logic()
    }
}

impl Debug for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOperator::*;
        match self {
            Not => write!(f, "!"),
            Neg => write!(f, "-"),
        }
    }
}

impl From<String> for UnaryOperator {
    fn from(value: String) -> Self {
        use UnaryOperator::*;
        match value.as_str() {
            "!" => Not,
            "-" => Neg,
            &_ => unimplemented!(),
        }
    }
}

#[derive(Clone)]
pub enum Expression<F, V> {
    // Infix op
    BinOp {
        dsym: DebugSymRef,
        op: BinaryOperator,
        lhs: Box<Expression<F, V>>,
        rhs: Box<Expression<F, V>>,
    },

    UnaryOp {
        dsym: DebugSymRef,
        op: UnaryOperator,
        sub: Box<Expression<F, V>>,
    },

    Select {
        dsym: DebugSymRef,
        cond: Box<Expression<F, V>>,
        when_true: Box<Expression<F, V>>,
        when_false: Box<Expression<F, V>>,
    },

    // Terminals
    Query(DebugSymRef, V),
    Const(DebugSymRef, F),
    True(DebugSymRef),
    False(DebugSymRef),
}

impl<F, V> Expression<F, V> {
    pub fn is_arith(&self) -> bool {
        use Expression::*;
        match self {
            BinOp { op, .. } => op.is_arith(),
            UnaryOp { op, .. } => op.is_arith(),
            Select {
                when_true,
                when_false,
                ..
            } => {
                assert_eq!(when_true.is_arith(), when_false.is_arith());

                when_true.is_arith()
            }
            Query(_, _) => true,
            Const(_, _) => true,
            True(_) => false,
            False(_) => false,
        }
    }

    pub fn is_logic(&self) -> bool {
        match self {
            Expression::BinOp { op, .. } => op.is_logic(),
            Expression::UnaryOp { op, .. } => op.is_logic(),
            Expression::Select {
                when_true,
                when_false,
                ..
            } => {
                assert_eq!(when_true.is_arith(), when_false.is_arith());

                when_true.is_logic()
            }
            _ => false,
        }
    }

    fn is_composed(&self) -> bool {
        match self {
            Expression::BinOp { .. } => true,
            Expression::UnaryOp { .. } => false,
            Expression::Select { .. } => true,

            Expression::Const(_, _) => false,
            Expression::Query(_, _) => false,
            Expression::True(_) => false,
            Expression::False(_) => false,
        }
    }
}

impl<F: Debug, V: Debug> Debug for Expression<F, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(_, arg0) => {
                let formatted = format!("{:?}", arg0);
                if formatted.starts_with("0x") {
                    let s = format!(
                        "0x{}",
                        formatted.trim_start_matches("0x").trim_start_matches('0')
                    );
                    write!(f, "{}", s)
                } else {
                    write!(f, "{}", formatted)
                }
            }

            Self::BinOp { op, lhs, rhs, .. } => {
                write!(
                    f,
                    "{} {:?} {}",
                    if lhs.is_composed() {
                        format!("({:?})", lhs)
                    } else {
                        format!("{:?}", lhs)
                    },
                    op,
                    if rhs.is_composed() {
                        format!("({:?})", rhs)
                    } else {
                        format!("{:?}", rhs)
                    }
                )
            }

            Self::Query(_, arg0) => write!(f, "{:?}", arg0),
            Expression::UnaryOp { .. } => todo!(),
            Expression::Select { .. } => todo!(),

            Expression::True(_) => write!(f, "true"),
            Expression::False(_) => write!(f, "false"),
        }
    }
}
