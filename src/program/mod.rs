//! Program representation.
//!
//! A program consists of a [`PredicateTable`](crate::program::predicate_table::PredicateTable)
//! mapping symbol/arity pairs to either sets of [`Clause`](crate::program::clause::Clause)s or
//! built-in predicate functions. During proof search, learned clauses are
//! collected in a [`Hypothesis`](crate::program::hypothesis::Hypothesis).

pub mod clause;
pub mod hypothesis;
pub mod predicate_table;
