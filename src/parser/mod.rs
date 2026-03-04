//! Prolog source parsing.
//!
//! Converts Prolog source text into compiled heap terms via three stages:
//! tokenisation ([`tokeniser`](crate::parser::tokeniser)), syntax tree
//! construction ([`build_tree`](crate::parser::build_tree)), and heap encoding
//! ([`execute_tree`](crate::parser::execute_tree)).

pub mod build_tree;
mod term;
pub mod tokeniser;
pub mod execute_tree;