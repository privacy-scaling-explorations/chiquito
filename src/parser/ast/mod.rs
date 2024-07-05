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
    /// Created by the compiler
    pub virt: bool,
}

impl DebugSymRef {
    pub fn new(start: usize, end: usize, file: Arc<SimpleFile<String, String>>) -> DebugSymRef {
        DebugSymRef {
            start,
            end,
            file,
            virt: false,
        }
    }

    pub fn virt(other: &DebugSymRef) -> DebugSymRef {
        let mut other = other.clone();
        other.virt = true;

        other
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

    /// Returns the proximity score of the given `offset` to the debug symbol in the file
    /// `filename`. The proximity score is calculated as the size of the symbol.
    /// If the offset is not within the symbol, returns `None`.
    pub fn proximity_score(&self, filename: &String, offset: usize) -> Option<usize> {
        if self.get_filename() == *filename && self.start <= offset && offset <= self.end {
            Some(self.end - self.start)
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
        } else {
            return write!(
                f,
                "nofile:{}:{}",
                self.get_line_start(),
                self.get_col_start()
            );
        }
    }
}

impl Eq for DebugSymRef {}

impl PartialEq for DebugSymRef {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end && self.file.name() == other.file.name()
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

    pub(crate) fn next(&self) -> Self {
        Self(self.0.clone(), self.1 + 1, self.2.clone())
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
            virt: false,
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
        let file_path = "file_path".to_string();
        let debug_sym_ref = DebugSymRef {
            start: 10,
            end: 12,
            file: Arc::new(SimpleFile::new(file_path.clone(), "".to_string())),
            virt: false,
        };

        assert_eq!(debug_sym_ref.proximity_score(&file_path, 9), None);
        assert_eq!(debug_sym_ref.proximity_score(&file_path, 10), Some(2));
        assert_eq!(
            debug_sym_ref.proximity_score(&"different_file_path".to_string(), 10),
            None
        );
        assert_eq!(debug_sym_ref.proximity_score(&file_path, 11), Some(2));
        assert_eq!(debug_sym_ref.proximity_score(&file_path, 12), Some(2));
        assert_eq!(debug_sym_ref.proximity_score(&file_path, 13), None);
    }
}
