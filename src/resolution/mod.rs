//! Resolution engine.
//!
//! Implements second-order SLD resolution with backtracking.
//! [`Proof`](crate::resolution::proof::Proof) drives the search,
//! [`unification`](crate::resolution::unification) handles term matching, and
//! [`build`](crate::resolution::build) constructs new terms from substitutions.

mod build;
mod env;
mod proof;
mod unification;
mod substitution;

pub use build::{build, re_build_bound_arg_terms};
use env::Env;
pub use proof::Proof;
pub use unification::unify;
pub use substitution::Substitution;