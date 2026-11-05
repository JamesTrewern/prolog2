//! Rejecting candidates that entail a negative example.
//!
//! Specialisation is a pass of its own, run after generalisation has merged
//! and deduplicated the sub hypotheses and their invented predicates'
//! definitions have been added to the predicate table: [`specialise`] filters
//! the deduplicated hypotheses against the negatives in parallel, and
//! [`clauses_entail_negative`] is applied again later to whole *combinations*
//! of sub hypotheses -- two that are each consistent can together entail a
//! negative, since a clause from one can resolve against a clause from the
//! other.
//!
//! Both prove the same question; [`clauses_entail_negative`] reports it the
//! way round its name says (`true` means a negative is provable, so the
//! candidate must go), while [`specialise`] returns the hypotheses that
//! survive.

use std::{
    io::{self, Write},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    heap::{ProgramHeap, QueryHeap},
    program::{Clause, PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::prelude::*;

/// Config for a test proof. Learning is turned off on the [`Proof`] itself,
/// not here; this only silences the debug trace. `max_depth` is kept to bound
/// recursive candidates.
fn test_config(config: Config) -> Config {
    Config {
        debug: false,
        ..config
    }
}

/// Does this set of ground clauses prove any negative example?
///
/// For candidates whose invented predicates have already been coined as
/// constants, which can be proved on a heap of their own. `neg_goals` are
/// addresses of goals compiled onto `heap` by
/// [`compile_examples`](super::utils::compile_examples).
///
/// `par_iter().any()` abandons the remaining negatives as soon as one is
/// proved.
pub(super) fn clauses_entail_negative(
    neg_goals: &[usize],
    clauses: &[Clause],
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    let config = test_config(config);

    neg_goals.into_par_iter().any(|&goal| {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::without_learning(&query_heap, &[goal]);
        proof.add_test_clauses(clauses);
        proof.prove(&mut query_heap, predicate_table, config)
    })
}

/// Filter out every hypothesis that proves a negative example.
///
/// Hypotheses are tested in parallel, one rayon task each; the negatives
/// *within* a hypothesis run serially, since with thousands of candidates the
/// pool is already saturated at the outer level and `any` wants to abandon a
/// candidate's remaining negatives the moment one is proved anyway.
///
/// Expects each hypothesis's invented predicates to have been grounded to
/// coined constants and their definitions added to `predicate_table`: the
/// clauses passed here are only the hypothesis's own top-level clauses, and a
/// goal on an invented predicate resolves through the table like any other
/// call. Ground clauses also mean there is nothing a test proof could bind,
/// so the hypotheses are shared read-only across the workers.
///
/// Survivors are returned in their original order.
pub(super) fn specialise(
    neg_goals: &[usize],
    hypotheses: Vec<Box<[Clause]>>,
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    config: Config,
) -> Vec<Box<[Clause]>> {
    if neg_goals.is_empty() {
        return hypotheses;
    }

    let config = test_config(config);
    let total = hypotheses.len();
    let tested = AtomicUsize::new(0);

    let retained: Vec<Box<[Clause]>> = hypotheses
        .into_par_iter()
        .filter(|hypothesis| {
            let keep = !neg_goals.iter().any(|&goal| {
                let mut query_heap = QueryHeap::new(heap, None);
                let mut proof = Proof::without_learning(&query_heap, &[goal]);
                proof.add_test_clauses(hypothesis);
                proof.prove(&mut query_heap, predicate_table, config)
            });

            // Throttled: one line per candidate would spend longer painting
            // the terminal than proving the negatives.
            let done = tested.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 256 == 0 || done == total {
                eprint!("\rSpecialise: {done}/{total} hypotheses tested  ");
                let _ = io::stderr().flush();
            }

            keep
        })
        .collect();

    eprintln!();
    retained
}
