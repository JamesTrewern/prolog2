//! # Prolog²
//!
//! A Meta-Interpretive Learning (MIL) framework implementing native second-order
//! SLD resolution. Prolog² extends traditional Prolog with the ability to learn
//! logical rules from examples through predicate invention.
//!
//! ## Library usage
//!
//! The primary use case for the library is writing custom predicate modules and
//! hooking them into the engine. The [`app::App`] builder handles configuration
//! loading, module registration, and execution.
//!
//! ```no_run
//! use std::process::ExitCode;
//! use std::sync::Arc;
//! use prolog2::{app::App, Config};
//! use prolog2::predicate_modules::{
//!     MATHS, META_PREDICATES, PredReturn, PredicateFunction, PredicateModule,
//! };
//! use prolog2::heap::query_heap::QueryHeap;
//! use prolog2::program::hypothesis::Hypothesis;
//! use prolog2::program::predicate_table::PredicateTable;
//!
//! fn my_pred(
//!     heap: &mut QueryHeap,
//!     hypothesis: &mut Hypothesis,
//!     goal: usize,
//!     pred_table: &PredicateTable,
//!     config: Config,
//! ) -> PredReturn {
//!     // Custom predicate logic here
//!     true.into()
//! }
//!
//! static MY_MODULE: PredicateModule = (&[
//!     ("my_pred", 1, my_pred),
//! ],&[]);
//!
//! fn main() -> ExitCode {
//!     App::from_args()
//!         .add_module(&MATHS)
//!         .add_module(&META_PREDICATES)
//!         .add_module(&MY_MODULE)
//!         .run()
//! }
//! ```

/// Application builder and configuration types.
pub mod app;
/// Heap memory management: cells, query heaps, and the symbol database.
pub mod heap;
/// Prolog source parsing: tokenisation, syntax tree construction, and term encoding.
pub mod parser;
/// Built-in predicate modules and the predicate module system.
pub mod predicate_modules;
/// Program representation: clauses, hypotheses, and the predicate table.
pub mod program;
/// Resolution engine: proof search, unification, and term building.
pub mod resolution;
/// Implementation of the Top Program Consturction algorithm with parallelism
pub mod top_prog;

// Re-export commonly used types at crate root.
pub use app::{BodyPred, Config, Examples, SetUp};

use std::fmt;
use crate::parser::ParserError;

#[derive(Debug)]
pub enum Error {
    IO(std::io::Error),
    Setup(serde_json::Error),
    Parser(ParserError),
    Query(String),
    BodyPred(String),
    Module(String),
}

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IO(e)      => write!(f, "IO error: {e}"),
            Self::Setup(e)   => write!(f, "setup error: {e}"),
            Self::Parser(e)  => write!(f, "parse error: {e}"),
            Self::Query(msg) => write!(f, "query error: {msg}"),
            Self::BodyPred(msg) => write!(f, "body predicate error: {msg}"),
            Self::Module(msg)   => write!(f, "module error: {msg}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::IO(e)     => Some(e),
            Self::Setup(e)  => Some(e),
            Self::Parser(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Error::IO(value)
    }
}

impl From<serde_json::Error> for Error {
    fn from(value: serde_json::Error) -> Self {
        Error::Setup(value)
    }
}

impl From<ParserError> for Error {
    fn from(value: ParserError) -> Self {
        Error::Parser(value)
    }
}


#[cfg(test)]
mod examples;
