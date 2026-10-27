use super::utils::parse_example;
use crate::{
    heap::{Cell, QueryHeap},
    program::{clause::Clause, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
pub(super) fn specialise_h(
    neg_examples: &[String],
    hypothesis: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    // Use the original max_depth to bound recursive hypotheses, but disable learning
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    for example in neg_examples {
        let mut query_heap = QueryHeap::new(heap, None);
        let goal = match parse_example(example, &mut query_heap) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Failed to parse negative example '{}': {}", example, e);
                continue;
            }
        };
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
pub(super) fn specialise_h_threaded(
    neg_examples: &[String],
    hypothesis: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    // Use the original max_depth to bound recursive hypotheses, but disable learning
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    !neg_examples.into_par_iter().any(|example| {
        let mut query_heap = QueryHeap::new(heap, None);
        let goal = match parse_example(example, &mut query_heap) {
            Ok(g) => g,
            Err(e) => {
                panic!("Failed to parse negative example '{}': {}", example, e);
            }
        };
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(hypothesis);
        // If any negative example is provable, reject this hypothesis
        proof.prove(&mut query_heap, predicate_table, config)
    })
}
