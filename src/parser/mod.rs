//! Prolog source parsing.
//!
//! Converts Prolog source text into compiled heap terms via three stages:
//! tokenisation ([`tokeniser`](crate::parser::tokeniser)), syntax tree
//! construction ([`build_tree`](crate::parser::build_tree)), and heap encoding
//! ([`execute_tree`](crate::parser::execute_tree)).

pub mod build_tree;
pub mod execute_tree;
mod term;
pub mod tokeniser;

use std::fmt;

#[derive(Debug)]
pub enum ParserError {
    // --- Lexer ---
    UnclosedStringLiteral { delimiter: char },
    UnclosedComment,
    InvalidEscapeSequence,
    // --- Parser: token-level ---
    /// Expected a specific token; `got: None` means EOF was reached instead.
    Expected { expected: String, got: Option<String> },
    UnexpectedToken { token: String },
    UnexpectedEof,
    // --- Parser: structural ---
    MalformedSet,
    /// Covers malformed existential-quantification syntax in meta-rules/meta-facts.
    MalformedMetaRule { detail: String },
    // --- Location wrapper ---
    /// Wraps any other variant with the source line number.
    AtLine { line: usize, cause: Box<ParserError> },
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnclosedStringLiteral { delimiter } =>
                write!(f, "unexpected end of file, missing closing `{delimiter}`"),
            Self::UnclosedComment =>
                write!(f, "unclosed multi-line comment"),
            Self::InvalidEscapeSequence =>
                write!(f, "invalid escape sequence"),
            Self::Expected { expected, got: Some(got) } =>
                write!(f, "expected `{expected}`, got `{got}`"),
            Self::Expected { expected, got: None } =>
                write!(f, "expected `{expected}`, got end of file"),
            Self::UnexpectedToken { token } =>
                write!(f, "unexpected token `{token}`"),
            Self::UnexpectedEof =>
                write!(f, "unexpected end of file"),
            Self::MalformedSet =>
                write!(f, "incorrectly formatted set"),
            Self::MalformedMetaRule { detail } =>
                write!(f, "malformed meta-rule: {detail}"),
            Self::AtLine { line, cause } =>
                write!(f, "line {line}: {cause}"),
        }
    }
}

impl std::error::Error for ParserError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::AtLine { cause, .. } => Some(cause),
            _ => None,
        }
    }
}