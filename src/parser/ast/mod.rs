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
    pub fn proximity_score(&self, offset: usize) -> Option<i32> {
        if self.start <= offset && offset <= self.end {
            Some(self.end as i32 - self.start as i32)
        } else {
            None
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

#[derive(Clone, PartialEq, Eq)]
pub struct Identifier(pub String, pub i32, pub DebugSymRef);
impl Identifier {
    pub(crate) fn new<S: AsRef<str>>(value: S, dsym: DebugSymRef) -> Self {
        let value_str = value.as_ref();
        Identifier(value_str.name(), value_str.rotation(), dsym)
    }

    pub(crate) fn debug_sym_ref(&self) -> DebugSymRef {
        self.2.clone()
    }
}

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

pub trait Identifiable {
    fn rotation(&self) -> i32;
    fn name(&self) -> String;
}

impl Identifiable for &str {
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
            0 => self.to_string(),
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
    use std::sync::Arc;

    use codespan_reporting::files::SimpleFile;

    use crate::parser::ast::{DebugSymRef, Identifier};

    #[test]
    fn test_from_string() {
        let debug_sym_ref = DebugSymRef {
            start: 0,
            end: 1,
            file: Arc::new(SimpleFile::new("file_path".to_string(), "".to_string())),
        };
        let result = Identifier::new("abc", debug_sym_ref.clone());

        assert_eq!(result.0, "abc");
        assert_eq!(result.1, 0);
        assert_eq!(result.2.start, debug_sym_ref.start);
        assert_eq!(result.2.end, debug_sym_ref.end);
        assert_eq!(*result.2.file.name(), *debug_sym_ref.file.name());

        let result = Identifier::new("abc'", debug_sym_ref.clone());

        assert_eq!(result.0, "abc");
        assert_eq!(result.1, 1);
        assert_eq!(result.2.start, debug_sym_ref.start);
        assert_eq!(result.2.end, debug_sym_ref.end);
        assert_eq!(*result.2.file.name(), *debug_sym_ref.file.name());
    }

    #[test]
    fn test_proximity_score() {
        let debug_sym_ref = DebugSymRef {
            start: 10,
            end: 12,
            file: Arc::new(SimpleFile::new("file_path".to_string(), "".to_string())),
        };

        assert_eq!(debug_sym_ref.proximity_score(9), None);
        assert_eq!(debug_sym_ref.proximity_score(10), Some(2_i32));
        assert_eq!(debug_sym_ref.proximity_score(11), Some(2_i32));
        assert_eq!(debug_sym_ref.proximity_score(12), Some(2_i32));
        assert_eq!(debug_sym_ref.proximity_score(13), None);
    }
}
