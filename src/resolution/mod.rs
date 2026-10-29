//! Resolution engine.
//!
//! Implements second-order SLD resolution with backtracking.
//! [`Proof`](crate::resolution::Proof) drives the search,
//! unification handles term matching, and
//! term building constructs new terms from substitutions.

mod build;
mod constraints;
#[allow(dead_code)]
#[allow(unused)]
mod env;
mod proof;
mod substitution;
mod unification;

// Public: what a native predicate needs to run a nested proof or to unify
// two terms itself, as `meta_predicates` and `defaults` do.
pub use proof::Proof;
pub use unification::unify;

// Internal: term construction and the substitution it threads through.
pub(crate) use build::build;
pub(crate) use substitution::Substitution;
