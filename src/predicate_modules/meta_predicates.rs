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
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: Arc<PredicateTable>,
    config: Config,
) -> PredReturn {
    use crate::heap::heap::Tag;

    // The goal is not(X), we want to prove X
    // Goal may be a Str cell pointing to the Func, or directly a Func cell
    // We need to find the actual Func cell first, then get the first argument

    // First dereference to handle any Ref indirection
    let mut func_addr = heap.deref_addr(goal);

    // If it's a Str cell, follow the pointer to the actual Func
    if let (Tag::Str, pointer) = heap[func_addr] {
        func_addr = pointer;
    }

    // Now func_addr points to: Func(2) | Con("not") | InnerGoal
    // The inner goal is at func_addr + 2
    // But it might be a Str cell pointing to the actual goal structure
    let arg_addr = func_addr + 2;
    let inner_goal = match heap[arg_addr] {
        (Tag::Str, pointer) => pointer, // Follow Str to actual goal
        (Tag::Ref, _) => heap.deref_addr(arg_addr), // Follow Ref chain
        _ => arg_addr,                  // Direct reference
    };

    // Create a config with learning disabled - we only want to test if the goal
    // can be proven with the CURRENT hypothesis, not learn new clauses
    let mut inner_config = config;
    inner_config.max_clause = 0; // Disable learning by not allowing new clauses

    let inner_heap = heap.branch(1).pop().unwrap();

    // Clone the current hypothesis so the inner proof can use the learned clauses
    // This is essential: we need to test if the inner goal succeeds given what
    // we've already learned. If it does, this hypothesis is bad and we backtrack.
    let hypothesis_clone = hypothesis.clone();
    let mut inner_proof = Proof::with_hypothesis(inner_heap, &[inner_goal], hypothesis_clone);

    if config.debug {
        eprintln!(
            "[NEGATE] {} with {} hypothesis clauses",
            inner_proof.heap.term_string(inner_goal),
            inner_proof.hypothesis.len()
        );
    }

    // Try to prove the inner goal with the current hypothesis
    // If it succeeds, not/1 fails (the hypothesis entails something it shouldn't)
    // If it fails, not/1 succeeds (the hypothesis correctly doesn't entail this)
    if inner_proof.prove(predicate_table, inner_config) {
        if config.debug {
            eprintln!(
                "[FAILED_TO_NEGATE] {}",
                inner_proof.heap.term_string(inner_goal)
            );
        }
        PredReturn::False
    } else {
        if config.debug {
            eprintln!(
                "[NEGATED_THROUGH_FAILURE] {}",
                inner_proof.heap.term_string(inner_goal)
            );
        }
        PredReturn::True
    }
}
