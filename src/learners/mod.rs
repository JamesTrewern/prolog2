//! Top Program Construction, parallelised.
//!
//! The stages, in the order [`parallel`] runs them:
//!
//! 1. **Generalise** (`parallel_mil`): each positive example is searched on
//!    its own thread for every sub hypothesis that proves it, and the
//!    predicates they invent are merged (`predicate_unification`).
//! 2. **Combine** (`sub_h_comb`): the sub hypotheses are profiled against
//!    the examples, filtered by the negative noise bound, searched for
//!    groups covering the positives, and the best hypotheses of those
//!    groups returned.

mod parallel_mil;
mod predicate_unification;
mod sub_h_comb;
mod utils;

pub(crate) use parallel_mil::parallel;
