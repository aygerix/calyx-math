//! Lexer, parser and syntax tree for the Magma language.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod span;
pub mod token;

pub use parser::{ParseError, parse_expression, parse_program, parse_program_prefix};
pub use span::{FileId, SourceFile, Span};

#[cfg(test)]
mod tests;
