use core::fmt::Debug;
use std::sync::Arc;

use codespan_reporting::files::{Files, SimpleFile};

pub mod debug_sym_factory;
pub mod expression;
pub mod statement;
pub mod tl;

/// Debug symbol reference, points to the source file, where a AST node comes from.
#[derive(Clone)]
pub struct DebugSymRef {
    /// Starting byte number in the file
    pub start: usize,
    /// Ending byte number in the file
    pub end: usize,
    /// Source file reference
    file: Arc<SimpleFile<String, String>>,
}

impl DebugSymRef {
    pub fn new(start: usize, end: usize, file: Arc<SimpleFile<String, String>>) -> DebugSymRef {
        DebugSymRef { start, end, file }
    }

    fn get_column_number(&self, line_index: usize, start: usize) -> usize {
        match self.file.column_number((), line_index, start) {
            Ok(number) => number,
            Err(err) => {
                panic!("Column number at {} not found: {}", line_index, err);
            }
        }
    }

    fn get_line_index(&self, start: usize) -> usize {
        match self.file.line_index((), start) {
            Ok(index) => index,
            Err(err) => {
                panic!("Line index at {} not found: {}", start, err);
            }
        }
    }

    fn get_line_number(&self, line_index: usize) -> usize {
        match self.file.line_number((), line_index) {
            Ok(number) => number,
            Err(err) => {
                panic!("Line number at {} not found: {}", line_index, err);
            }
        }
    }

    fn get_line_start(&self) -> usize {
        let line_idx = self.get_line_index(self.start);
        self.get_line_number(line_idx)
    }

    fn get_col_start(&self) -> usize {
        let line_idx = self.get_line_index(self.start);
        self.get_column_number(line_idx, self.start)
    }

    fn get_line_end(&self) -> usize {
        let line_idx = self.get_line_index(self.end);
        self.get_line_number(line_idx)
    }

    fn get_col_end(&self) -> usize {
        let line_idx = self.get_line_index(self.end);
        self.get_column_number(line_idx, self.end)
    }

    pub(crate) fn get_filename(&self) -> String {
        self.file.name().to_string()
    }

    /// Returns the proximity score of the given offset to the debug symbol.
    /// The proximity score is the sum of the distance from the start and end of the symbol.
    /// If the offset is not within the symbol, -1 is returned.
    pub fn proximity_score(&self, offset: usize) -> i32 {
        if self.start <= offset && offset <= self.end {
            let start_diff = offset as i32 - self.start as i32;
            let end_diff = self.end as i32 - offset as i32;

            start_diff + end_diff
        } else {
            -1
        }
    }
}

impl Debug for DebugSymRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.file.name().is_empty() {
            // Produces clickable output in the terminal
            return write!(
                f,
                "{}:{}:{}",
                self.file.name(),
                self.get_line_start(),
                self.get_col_start()
            );
        }

        let mut debug_print = f.debug_struct("DebugSymRef");

        if self.get_line_start() == self.get_line_end() {
            debug_print.field("line", &self.get_line_start()).field(
                "cols",
                &format!("{}-{}", self.get_col_start(), self.get_col_end()),
            );
        } else {
            debug_print
                .field(
                    "start",
                    &format!("{}:{}", self.get_line_start(), self.get_col_start()),
                )
                .field(
                    "end",
                    &format!("{}:{}", self.get_line_end(), self.get_col_end()),
                );
        }

        debug_print.finish()
    }
}

#[derive(Clone)]
pub struct Identifier(pub String, pub i32);

impl Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 == 0 {
            write!(f, "{}", self.0)
        } else if self.1 == 1 {
            write!(f, "{}'", self.0)
        } else {
            write!(f, "{}#{}", self.0, self.1)
        }
    }
}

impl From<String> for Identifier {
    fn from(value: String) -> Self {
        Identifier(value.name(), value.rotation())
    }
}

impl From<&str> for Identifier {
    fn from(value: &str) -> Self {
        Identifier::from(value.to_string())
    }
}

pub trait Identifiable {
    fn rotation(&self) -> i32;
    fn name(&self) -> String;
}

impl Identifiable for String {
    fn rotation(&self) -> i32 {
        assert!(!self.is_empty());
        let last = self.chars().last().unwrap();

        if last == '\'' {
            1
        } else {
            0
        }
    }

    fn name(&self) -> String {
        let rot = self.rotation();

        match rot {
            0 => self.clone(),
            1 => {
                let mut chars = self.chars();
                chars.next_back();

                chars.as_str().to_string()
            }
            _ => unimplemented!(),
        }
    }
}

impl Identifiable for Identifier {
    fn rotation(&self) -> i32 {
        self.1
    }

    fn name(&self) -> String {
        self.0.clone()
    }
}

#[cfg(test)]
mod test {
    use crate::parser::ast::Identifier;

    #[test]
    fn test_from_string() {
        let result = Identifier::from("abc");

        assert_eq!(result.0, "abc");
        assert_eq!(result.1, 0);

        let result = Identifier::from("abc'");

        assert_eq!(result.0, "abc");
        assert_eq!(result.1, 1);
    }
}
