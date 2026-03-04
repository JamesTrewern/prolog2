//! Resolution engine.
//!
//! Implements second-order SLD resolution with backtracking.
//! [`Proof`](crate::resolution::proof::Proof) drives the search,
//! [`unification`](crate::resolution::unification) handles term matching, and
//! [`build`](crate::resolution::build) constructs new terms from substitutions.

pub mod unification;
pub mod build;
pub mod proof;
#[cfg(test)]
mod constraint_tests;
