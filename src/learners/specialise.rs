//! Rejecting candidates that entail a negative example.
//!
//! Specialisation is no longer a pass of its own. Each worker applies
//! [`hypothesis_entails_negative`] to a sub hypothesis the moment the search
//! finds it, so nothing that proves a negative is ever collected, and
//! [`clauses_entail_negative`] is applied again later to whole *combinations*
//! of sub hypotheses -- two that are each consistent can together entail a
//! negative, since a clause from one can resolve against a clause from the
//! other.
//!
//! Both answer the same question and both report it the same way round:
//! `true` means a negative is provable, so the candidate must go.

use crate::{
    heap::{Cell, QueryHeap},
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::prelude::*;

/// Learning disabled, so a negative is tested against the candidate rather
/// than extended into a new hypothesis. `max_depth` is kept to bound
/// recursive candidates.
fn test_config(config: Config) -> Config {
    Config {
        max_depth: config.max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
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
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    let config = test_config(config);

    neg_goals.into_par_iter().any(|&goal| {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(clauses);
        proof.prove(&mut query_heap, predicate_table, config)
    })
}

/// Does this hypothesis, still mid-search, prove any negative example?
///
/// Each negative gets its own [branch](QueryHeap::branch) of the search heap:
/// a heap that reads the program cells and everything the search has built --
/// including the hypothesis clause literals, which exist nowhere else -- but
/// writes only its own cells and its own copy of the variable registers. The
/// branches are therefore independent, so the negatives run in parallel and
/// `any` abandons the rest the moment one is proved.
///
/// Nothing needs undoing afterwards. A branch cannot touch its parent's cells
/// (`IndexMut` refuses them) and binds only its copied registers, so dropping
/// it restores the search heap by construction.
///
/// [`Proof::with_hypothesis`] clones the whole hypothesis, so the inner proof
/// inherits the constraint set and the invented-predicate registry. That
/// matters here and not in [`clauses_entail_negative`]: the invented
/// predicates are still unbound variables at this point, and without the
/// registry a goal on one would resolve against a background fact and
/// collapse the invention, failing a negative the real hypothesis does not
/// entail.
pub(super) fn hypothesis_entails_negative(
    neg_goals: &[usize],
    hypothesis: &Hypothesis,
    heap: &QueryHeap,
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    if neg_goals.is_empty() {
        return false;
    }
    let config = test_config(config);

    let mut branches = heap.branch(neg_goals.len());
    branches
        .par_iter_mut()
        .zip(neg_goals.par_iter())
        .any(|(branch, &goal)| {
            let mut inner = Proof::with_hypothesis(branch, &[goal], hypothesis);
            inner.prove(branch, predicate_table, config)
        })
}
