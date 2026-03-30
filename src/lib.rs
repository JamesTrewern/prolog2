//! # Prolog²
//!
//! A Meta-Interpretive Learning (MIL) framework implementing native second-order
//! SLD resolution. Prolog² extends traditional Prolog with the ability to learn
//! logical rules from examples through predicate invention.
//!
//! ## Library usage
//!
//! The main extension point is the **predicate module** system. A
//! [`predicate_modules::PredicateModule`] bundles native Rust predicate functions
//! together with optional Prolog source code. Modules are registered with the
//! [`app::App`] builder, which also handles configuration loading and execution.
//!
//! ### Writing a native predicate
//!
//! A native predicate is a Rust function with the signature defined by
//! [`predicate_modules::PredicateFunction`]. It receives the current heap, the
//! hypothesis being constructed, the heap address of the goal term, the predicate
//! table, and the engine configuration. It returns a [`predicate_modules::PredReturn`]
//! indicating:
//!
//! - [`PredReturn::True`] — success with no heap side-effects.
//! - [`PredReturn::False`] — deterministic failure; the engine backtracks.
//! - [`PredReturn::Success`] — success with a list of `(source, target)` variable
//!   bindings to apply on the heap, and an optional list of new sub-goals to resolve.
//!
//! For the common case of a simple boolean check, `bool` converts directly via
//! `Into<PredReturn>`.
//!
//! ```no_run
//! use std::process::ExitCode;
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
//! ], &[]);
//!
//! fn main() -> ExitCode {
//!     let app = App::new()
//!         .load_module(&MATHS).expect("failed to load MATHS")
//!         .load_module(&META_PREDICATES).expect("failed to load META_PREDICATES")
//!         .load_module(&MY_MODULE).expect("failed to load MY_MODULE");
//!     app.run()
//! }
//! ```
//!
//! ## Error handling
//!
//! Fallible operations return [`Result<T>`], a type alias for
//! `std::result::Result<T, `[`Error`]`>`. The [`Error`] enum covers all error
//! categories the engine can produce:
//!
//! - [`Error::IO`] — I/O errors when reading source files.
//! - [`Error::Setup`] — JSON deserialisation failures for `setup.json`.
//! - [`Error::Parser`] — structured parse errors from the Prolog parser; wraps a
//!   [`parser::ParserError`] which carries source-line information via its
//!   `AtLine` variant.
//! - [`Error::Query`] — a query could not be executed (e.g. bad goal syntax).
//! - [`Error::BodyPred`] — a body-predicate specification in the setup is invalid.
//! - [`Error::Module`] — a predicate module could not be loaded (e.g. duplicate predicate).

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

use crate::parser::ParserError;
use std::fmt;

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
            Self::IO(e) => write!(f, "IO error: {e}"),
            Self::Setup(e) => write!(f, "setup error: {e}"),
            Self::Parser(e) => write!(f, "parse error: {e}"),
            Self::Query(msg) => write!(f, "query error: {msg}"),
            Self::BodyPred(msg) => write!(f, "body predicate error: {msg}"),
            Self::Module(msg) => write!(f, "module error: {msg}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::IO(e) => Some(e),
            Self::Setup(e) => Some(e),
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
