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
//! use prolog2::app::{APP, Config};
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
//!     pred_table: Arc<PredicateTable>,
//!     config: Config,
//! ) -> PredReturn {
//!     // Custom predicate logic here
//!     PredReturn::True
//! }
//!
//! static MY_MODULE: PredicateModule = &[
//!     ("my_pred", 1, my_pred),
//! ];
//!
//! fn main() -> ExitCode {
//!     Prolog2::from_args()
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

// Re-export commonly used types at crate root.
pub use app::{BodyClause, Config, Examples, SetUp};

#[cfg(test)]
mod examples;
