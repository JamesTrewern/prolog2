use super::utils::parse_example;
use crate::{
    heap::{Cell, QueryHeap},
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use smallvec::SmallVec;

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
fn specialise_h(
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

    // Build a Hypothesis from the clauses so we can use Proof::with_hypothesis
    let mut h = Hypothesis::new();
    for clause in hypothesis {
        h.push_clause(clause.clone(), SmallVec::new());
    }

    for example in neg_examples {
        let mut query_heap = QueryHeap::new(heap, None);
        let goal = match parse_example(example, &mut query_heap) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Failed to parse negative example '{}': {}", example, e);
                continue;
            }
        };
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h);
        // If any negative example is provable, reject this hypothesis
        if proof.prove(&mut query_heap, predicate_table, config) {
            return false;
        }
        // Reclaim the hypothesis — it was never mutated since max_clause is 0
        h = std::mem::replace(&mut proof.hypothesis, Hypothesis::new());
    }
    true
}

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
fn specialise_h_threaded(
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
        let mut h = Hypothesis::new();
        for clause in hypothesis {
            h.push_clause(clause.clone(), SmallVec::new());
        }
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h);
        // If any negative example is provable, reject this hypothesis
        proof.prove(&mut query_heap, predicate_table, config)
    })
}
