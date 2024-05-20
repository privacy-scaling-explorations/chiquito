use core::fmt::Debug;

pub mod debug_sym_factory;
pub mod expression;
pub mod statement;
pub mod tl;

/// Debug symbol reference, points to the source file, where a AST node comes from.
#[derive(Clone)]
pub struct DebugSymRef {
    /// Starting line number in the file
    pub line_start: usize,
    /// Starting column number in the file
    pub col_start: usize,
    /// Ending line number in the file
    pub line_end: usize,
    /// Ending column number in the file
    pub col_end: usize,
    /// Source file name
    pub file_name: String,
}

impl DebugSymRef {
    pub fn new(
        line_start: usize,
        col_start: usize,
        line_end: usize,
        col_end: usize,
        file_name: String,
    ) -> DebugSymRef {
        DebugSymRef {
            line_start,
            col_start,
            line_end,
            col_end,
            file_name,
        }
    }
}

impl Debug for DebugSymRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.file_name.is_empty() {
            // Produces clickable output in the terminal
            return write!(
                f,
                "{}:{}:{}",
                self.file_name, self.line_start, self.col_start
            );
        }

        let mut debug_print = f.debug_struct("DebugSymRef");

        if self.line_start == self.line_end {
            debug_print
                .field("line", &self.line_start)
                .field("cols", &format!("{}-{}", self.col_start, self.col_end));
        } else {
            debug_print
                .field("start", &format!("{}:{}", self.line_start, self.col_start))
                .field("end", &format!("{}:{}", self.line_end, self.col_end));
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
