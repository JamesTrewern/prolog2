//! Rejecting candidates that entail a negative example.
//!
//! Specialisation is a pass of its own, run after generalisation has merged
//! and deduplicated the sub hypotheses: [`specialise`] filters them against
//! the negatives in parallel, proving from `MetaSub`s, and
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
    program::{Clause, PackedMetaSubs, PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::prelude::*;

use super::predicate_unification::PredDefTable;

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
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], clauses);
        proof.prove(&mut query_heap, predicate_table, config)
    })
}

/// Indices of the hypotheses that prove no negative example, in order.
/// Hypotheses are tested in parallel, one rayon task each; the negatives
/// *within* a hypothesis run serially
pub(super) fn specialise(
    neg_goals: &[usize],
    hypotheses: &PackedMetaSubs,
    pdt: &PredDefTable,
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    config: Config,
) -> Vec<u32> {
    let total = u32::try_from(hypotheses.len()).expect("more than u32::MAX hypotheses");
    if neg_goals.is_empty() {
        return (0..total).collect();
    }

    let config = test_config(config);
    let tested = AtomicUsize::new(0);

    let retained: Vec<u32> = (0..total)
        .into_par_iter()
        .filter(|&index| {
            let meta_subs = pdt.test_meta_subs(hypotheses.get(index as usize), heap);
            let keep = !neg_goals.iter().any(|&goal| {
                let mut query_heap = QueryHeap::new(heap, None);
                let mut proof = Proof::with_hypothesis(&query_heap, &[goal], meta_subs.as_slice());
                proof.prove(&mut query_heap, predicate_table, config)
            });

            // Throttled: one line per candidate would spend longer painting
            // the terminal than proving the negatives.
            let done = tested.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 256 == 0 || done == total as usize {
                eprint!("\rSpecialise: {done}/{total} hypotheses tested  ");
                let _ = io::stderr().flush();
            }

            keep
        })
        .collect();

    eprintln!();
    retained
}
