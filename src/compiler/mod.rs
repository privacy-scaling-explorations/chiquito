use std::hash::Hash;

use self::compiler::{Compiler, CompilerResult};
use crate::{field::Field, parser::ast::DebugSymRef};

pub mod abepi;
#[allow(clippy::module_inception)]
pub mod compiler;
pub mod semantic;
mod setup_inter;

#[derive(Default)]
pub struct Config {
    pub(self) max_degree: Option<usize>,
}

impl Config {
    pub fn max_degree(mut self, degree: usize) -> Self {
        self.max_degree = Some(degree);

        self
    }
}

/// Compiler message.
#[derive(Debug, Clone)]
pub enum Message {
    ParseErr {
        msg: String,
    },
    /// Semantic Error
    SemErr {
        msg: String,
        dsym: DebugSymRef,
    },
    RuntimeErr {
        msg: String,
        dsym: DebugSymRef,
    },
}

/// Collection of compiler messages.
pub trait Messages {
    fn has_errors(&self) -> bool;
}

impl Messages for Vec<Message> {
    fn has_errors(&self) -> bool {
        // currently all messages are errors
        !self.is_empty()
    }
}

/// Compiles chiquito source code into a SBPIR, also returns messages.
pub fn compile<F: Field + Hash>(
    source: &str,
    config: Config,
) -> Result<CompilerResult<F>, Vec<Message>> {
    Compiler::new(config).compile(source)
}
