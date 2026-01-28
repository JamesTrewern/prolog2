use std::sync::Arc;

use crate::{
    heap::{heap::Heap, query_heap::QueryHeap},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::proof::Proof,
    Config,
};

use super::PredReturn;

/// Negation as failure: succeeds if the inner goal cannot be proven
pub fn not(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: Arc<PredicateTable>,
    config: Config,
) -> PredReturn {
    // The goal is not(X), we want to prove X
    // Goal structure: Str -> Func(2) | Con("not") | InnerGoal
    // The inner goal is at goal + 2 (after the Func cell and the 'not' symbol)
    let inner_goal = heap.deref_addr(goal + 2);

    // Create a config with learning disabled
    let mut inner_config = config;
    inner_config.max_clause = 0; // Disable learning by not allowing new clauses
    inner_config.debug = false;


    let inner_heap = heap.branch(1).pop().unwrap();

    // Create a new proof for the inner goal with an empty hypothesis
    // We don't want to inherit or modify the current hypothesis during negation check
    let mut inner_proof = Proof::new(inner_heap, &[inner_goal]);


    // Try to prove the inner goal
    // If it succeeds, not/1 fails; if it fails, not/1 succeeds
    if inner_proof.prove(predicate_table, inner_config) {
        PredReturn::False
    } else {
        PredReturn::True
    }
}
