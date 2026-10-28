//! Top Program Construction, parallelised.
//!
//! Generalisation and specialisation are not separate passes. Each positive
//! example is searched on its own thread, and every sub hypothesis the search
//! produces is tested against the negatives as soon as it is found, so only
//! consistent ones are ever collected. What remains afterwards is combining
//! them: merging the predicate definitions they invent, then choosing
//! covering groups that stay consistent together.

mod parallel_mil;
mod predicate_unification;
mod specialise;
mod sub_h_unification;
mod utils;
