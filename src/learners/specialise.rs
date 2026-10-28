use crate::{
    heap::{Cell, QueryHeap},
    program::{clause::Clause, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
///
/// `neg_goals` are addresses of goals already compiled onto `heap` by
/// [`compile_examples`](super::utils::compile_examples).
pub(super) fn specialise_h(
    neg_goals: &[usize],
    hypothesis: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    // Use the original max_depth to bound recursive hypotheses, but disable learning
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    for &goal in neg_goals {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(hypothesis);
        // If any negative example is provable, reject this hypothesis
        if proof.prove(&mut query_heap, predicate_table, config) {
            return false;
        }
    }
    true
}

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
/// As [`specialise_h`], testing the negatives in parallel.
///
/// `par_iter().any()` stops the whole search as soon as one negative is
/// proved, so the remaining negatives are abandoned rather than run to
/// completion.
pub(super) fn specialise_h_threaded(
    neg_goals: &[usize],
    hypothesis: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    // Use the original max_depth to bound recursive hypotheses, but disable learning
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    !neg_goals.into_par_iter().any(|&goal| {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(hypothesis);
        // If any negative example is provable, reject this hypothesis
        proof.prove(&mut query_heap, predicate_table, config)
    })
}
