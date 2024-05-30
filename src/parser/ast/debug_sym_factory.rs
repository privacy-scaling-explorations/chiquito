use std::sync::Arc;

use codespan_reporting::files::SimpleFile;

use super::DebugSymRef;

/// Factory for creating debug symbol references.
pub struct DebugSymRefFactory {
    /// Source file reference.
    file: Arc<SimpleFile<String, String>>,
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
        let file = Arc::new(SimpleFile::new(file_path.to_string(), contents.to_string()));

        DebugSymRefFactory { file }
    }

    /// Creates a new debug symbol reference.
    ///
    /// # Arguments
    ///
    /// * `start` - Start position of the debug symbol byte reference in the source string.
    /// * `end` - End position of the debug symbol byte reference in the source string.
    pub fn create(&self, start: usize, end: usize) -> DebugSymRef {
        DebugSymRef::new(start, end, Arc::clone(&self.file))
    }
}
