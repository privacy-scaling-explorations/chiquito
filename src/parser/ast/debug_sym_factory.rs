use codespan_reporting::files::{Files, SimpleFile};

use super::DebugSymRef;

/// Factory for creating debug symbol references.
pub struct DebugSymRefFactory {
    /// Source file.
    file: SimpleFile<String, String>,
}

impl DebugSymRefFactory {
    /// Creates a new debug symbol reference factory.
    ///
    /// # Arguments
    ///
    /// * `file_path` - Path to the source file.
    /// * `contents` - Contents of the source file.
    ///
    /// # Returns
    ///
    /// A new debug symbol reference factory.
    pub fn new(file_path: &str, contents: &str) -> DebugSymRefFactory {
        let file = SimpleFile::new(file_path.to_string(), contents.to_string());

        DebugSymRefFactory { file }
    }

    /// Creates a new debug symbol reference.
    ///
    /// # Arguments
    ///
    /// * `start` - Start position of the debug symbol byte reference in the source string.
    /// * `end` - End position of the debug symbol byte reference in the source string.
    pub fn create(&self, start: usize, end: usize) -> DebugSymRef {
        let start_line_index = self.get_line_index(start);
        let start_line_number = self.get_line_number(start_line_index);
        let start_col_number = self.get_column_number(start_line_index, start);

        let end_line_index = self.get_line_index(end);
        let end_line_number = self.get_line_number(end_line_index);
        let end_col_number = self.get_column_number(end_line_index, end);

        DebugSymRef::new(
            start_line_number,
            start_col_number,
            end_line_number,
            end_col_number,
            self.file.name().to_string(),
        )
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
}
