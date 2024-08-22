use std::{
    fs::File,
    hash::Hash,
    io::{self, Read},
};

use compiler::{Compiler, CompilerResult};
use compiler_legacy::{CompilerLegacy, CompilerResultLegacy};

use crate::{
    field::Field,
    parser::ast::{debug_sym_factory::DebugSymRefFactory, DebugSymRef},
};

pub mod abepi;
#[allow(clippy::module_inception)]
pub mod compiler;
pub mod compiler_legacy;
pub mod semantic;
mod setup_inter;

#[derive(Default)]
pub struct Config {
    pub(self) max_degree: Option<usize>,
    pub(self) max_steps: usize,
}

impl Config {
    pub fn max_degree(mut self, degree: usize) -> Self {
        self.max_degree = Some(degree);

        self
    }

    pub fn max_steps(mut self, steps: usize) -> Self {
        self.max_steps = steps;

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

/// Compiles chiquito source code string into a SBPIR for a single machine, also returns messages
/// (legacy).
pub fn compile_legacy<F: Field + Hash>(
    source: &str,
    config: Config,
    debug_sym_ref_factory: &DebugSymRefFactory,
) -> Result<CompilerResultLegacy<F>, Vec<Message>> {
    CompilerLegacy::new(config).compile(source, debug_sym_ref_factory)
}

/// Compiles chiquito source code file into a SBPIR for a single machine, also returns messages
/// (legacy).
pub fn compile_file_legacy<F: Field + Hash>(
    file_path: &str,
    config: Config,
) -> Result<CompilerResultLegacy<F>, Vec<Message>> {
    let contents = read_file(file_path);
    match contents {
        Ok(source) => {
            let debug_sym_ref_factory = DebugSymRefFactory::new(file_path, source.as_str());
            compile_legacy(source.as_str(), config, &debug_sym_ref_factory)
        }
        Err(e) => {
            let msg = format!("Error reading file: {}", e);
            let message = Message::ParseErr { msg };
            let messages = vec![message];

            Err(messages)
        }
    }
}

/// Compiles chiquito source code string into a SBPIR, also returns messages.
pub fn compile<F: Field + Hash>(
    source: &str,
    config: Config,
    debug_sym_ref_factory: &DebugSymRefFactory,
) -> Result<CompilerResult<F>, Vec<Message>> {
    Compiler::new(config).compile(source, debug_sym_ref_factory)
}

/// Compiles chiquito source code file into a SBPIR, also returns messages.
pub fn compile_file<F: Field + Hash>(
    file_path: &str,
    config: Config,
) -> Result<CompilerResult<F>, Vec<Message>> {
    let contents = read_file(file_path);
    match contents {
        Ok(source) => {
            let debug_sym_ref_factory = DebugSymRefFactory::new(file_path, source.as_str());
            compile(source.as_str(), config, &debug_sym_ref_factory)
        }
        Err(e) => {
            let msg = format!("Error reading file: {}", e);
            let message = Message::ParseErr { msg };
            let messages = vec![message];

            Err(messages)
        }
    }
}

fn read_file(path: &str) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}
