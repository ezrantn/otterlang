use std::fmt;

use crate::ast::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum CheckError {
    UseAfterMove { var: String },
    TypeMismatch { expected: Type, found: Type },
    InvalidIndex { base_ty: Type },
    UndefinedVariable { var: String },
    UndefinedArray { var: String },
    ArrayOutOfBound { var: String },
    AssignToMoved { var: String },
    TypeError { var: String },
    GenericError(String),
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "mismatched types\nexpected: {:?}\n   found: {:?}",
                    expected, found
                )
            }
            CheckError::InvalidIndex { base_ty } => {
                write!(f, "cannot index into a value of type `{:?}`", base_ty)
            }
            CheckError::TypeError { var } => {
                write!(f, "{}", var) // Here 'var' is actually the custom message
            }
            CheckError::UndefinedVariable { var } => {
                write!(f, "cannot find value `{}` in this scope", var)
            }
            CheckError::UseAfterMove { var } => {
                write!(f, "use of moved value: '{}'", var)
            }
            CheckError::UndefinedArray { var } => write!(f, "array `{}` is undefined", var),
            CheckError::ArrayOutOfBound { var } => {
                write!(f, "index out of bounds for array `{}`", var)
            }
            CheckError::GenericError(msg) => write!(f, "{}", msg),
            // ... other variants
            _ => write!(f, "{:?}", self),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub error: CheckError,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        Span { start, end }
    }

    /// Dummy span for tests, desugaring, or generated code
    pub fn dummy() -> Self {
        Span { start: 0, end: 0 }
    }

    /// Length in bytes
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    // 0..0 is both empty and dummy
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // 5..5 is empty but not dummy
    pub fn is_dummy(&self) -> bool {
        self.start == 0 && self.end == 0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    pub fn dummy(node: T) -> Self {
        Self {
            node,
            span: Span::dummy(),
        }
    }
}

impl Diagnostic {
    pub fn emit(&self, source: &str) {
        let line_num = source[..self.span.start].lines().count();
        let snippet = &source[self.span.start..self.span.end];

        println!("error: {}", self.error); // Use the error's display
        println!("  --> line {}", line_num);
        println!("   |");
        println!("{:3} |  {}", line_num, snippet);
        // Calculate underlining
        println!("   |  {}", "^".repeat(self.span.len()));
        println!("   |");
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.error {
            CheckError::UseAfterMove { var } => {
                write!(
                    f,
                    "Borrow error: use of moved value '{}'\n  at {:?}",
                    var, self.span
                )
            }
            CheckError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "Type error: expected '{}', found '{}'\n  at {:?}",
                    expected, found, self.span
                )
            }
            CheckError::InvalidIndex { base_ty } => {
                write!(
                    f,
                    "Type error: cannot index into value of type '{}'\n  at {:?}",
                    base_ty, self.span
                )
            }
            CheckError::UndefinedVariable { var } => {
                write!(f, "Variable '{}' undefined\n at {:?}", var, self.span)
            }
            CheckError::AssignToMoved { var } => {
                write!(
                    f,
                    "Borrow Error: Cannot assign to moved or uninitialized '{}'\n at {:?}",
                    var, self.span
                )
            }
            CheckError::UndefinedArray { var } => {
                write!(f, "Array '{}' undefined\n at {:?}", var, self.span)
            }
            CheckError::ArrayOutOfBound { var } => {
                write!(f, "Array '{}' out of bound\n at {:?}", var, self.span)
            }
            CheckError::TypeError { var } => {
                write!(f, "Type error: {}\n at {:?}", var, self.span)
            }
            CheckError::GenericError(var) => {
                write!(f, "{}", var)
            }
        }
    }
}
