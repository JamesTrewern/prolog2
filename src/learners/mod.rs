//! Top Program Construction, parallelised.
//!
//! The stages, in the order [`parallel`] runs them:
//!
//! 1. **Generalise** (`parallel_mil`): each positive example is searched on
//!    its own thread for every sub hypothesis that proves it, and the
//!    predicates they invent are merged (`predicate_unification`).
//! 2. **Profile** (`coverage`): every example is proved against every sub
//!    hypothesis, once.
//! 3. **Filter** (`coverage`, `noise`): the sub hypotheses within the
//!    negative noise bound are kept. A positive none of them proves ends
//!    the run with a report (`noise_report`), unless it may be left.
//! 4. **Search** (`search`): groups of sub hypotheses covering the
//!    positives are built from the profiles alone.
//! 5. **Pool** (`pool`): each group's hypothesis is reduced, proved and
//!    ranked, and the best returned.

mod coverage;
mod noise;
mod noise_report;
mod parallel_mil;
mod pool;
mod predicate_unification;
mod search;
mod utils;

pub(crate) use parallel_mil::parallel;
