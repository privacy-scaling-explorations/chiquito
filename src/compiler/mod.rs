use std::{
    fs::File,
    hash::Hash,
    io::{self, Read},
};

use self::compiler::{Compiler, CompilerResult};
use crate::{
    field::Field,
    parser::ast::{debug_sym_factory::DebugSymRefFactory, DebugSymRef},
};

pub mod abepi;
#[allow(clippy::module_inception)]
pub mod compiler;
pub mod semantic;
mod setup_inter;
mod cse;

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
