//! Resolution engine.
//!
//! Implements second-order SLD resolution with backtracking.
//! [`Proof`](crate::resolution::proof::Proof) drives the search,
//! [`unification`](crate::resolution::unification) handles term matching, and
//! [`build`](crate::resolution::build) constructs new terms from substitutions.

pub mod build;
#[cfg(test)]
mod constraint_tests;
pub mod proof;
pub mod unification;
