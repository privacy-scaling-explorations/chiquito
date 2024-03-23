use core::fmt::Debug;

pub mod expression;
pub mod statement;
pub mod tl;

/// Debug symbol reference, points to the source file, where a AST node comes from.
// TODO: scafolding struct that should be implemented fully.
#[derive(Clone, Debug)]
pub struct DebugSymRef {
    /// Start char position on the source file.
    pub start: usize,
    /// End char position on the source file.
    pub end: usize,
    // TODO: more fields will be added as needed, like file name, etc...
}

impl DebugSymRef {
    pub fn new(start: usize, end: usize) -> DebugSymRef {
        DebugSymRef { start, end }
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
