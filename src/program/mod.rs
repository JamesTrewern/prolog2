//! Program representation.
//!
//! A program is a [`PredicateTable`](crate::program::PredicateTable) mapping
//! symbol/arity pairs to either sets
//! of clauses or built-in predicate functions. During proof search, learned
//! clauses are collected in a [`Hypothesis`](crate::program::Hypothesis).
//!
//! Both types appear in the signature of a native predicate (see
//! [`PredicateFunction`](crate::predicate_modules::PredicateFunction)), so
//! both are public; the rest of the representation is internal.

mod clause;
mod hypothesis;
mod meta_sub;
mod predicate_table;

// Public: named by every native predicate's signature.
pub use hypothesis::Hypothesis;
pub use predicate_table::PredicateTable;

// Internal: the shape of a clause, and the pieces that build and compare one.
pub(crate) use clause::{BitFlag64, Clause, MetaData, MAX_ARG};
// Only the learners' tests build a constraint set directly.
#[cfg(test)]
pub(crate) use hypothesis::Constraints;
pub(crate) use meta_sub::MetaSub;
pub(crate) use predicate_table::Predicate;
