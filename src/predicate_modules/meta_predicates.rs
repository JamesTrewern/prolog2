use std::collections::HashMap;

use crate::{
    Config, heap::{
        heap::Heap,
        query_heap::QueryHeap,
    }, predicate_modules::helpers::{goal_arg, resolve}, program::{hypothesis::Hypothesis, predicate_table::PredicateTable}, resolution::proof::Proof
};

use super::{PredReturn, PredicateModule};

/// Negation as failure: succeeds if the inner goal cannot be proven
pub fn not(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    // Create a config with learning disabled - we only want to test if the goal
    // can be proven with the CURRENT hypothesis, not learn new clauses
    let mut inner_config = config;
    inner_config.max_clause = 0; // Disable learning by not allowing new clauses

    //Create new heap by branching the current heap, then duplicate goal to mutable cells of inner_heap
    //TODO Proof does not need ownership of query heap so this step would be easier is heap could be passed to the inner proof directly
    let mut inner_heap = heap.branch(1).pop().unwrap();
    let inner_goal = inner_heap.dup_term(resolve(&inner_heap, goal_arg(&inner_heap, goal, 0)),&mut HashMap::new());

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

///find_all(+Template,:Goal,-Bag)
pub fn findall(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

/// Built-in meta-predicates: `not/1` (negation as failure).
pub static META_PREDICATES: PredicateModule = (
    &[
        ("not", 1, not),
        ("findall", 3, findall),
    ],
    &[include_str!("../../builtins/meta_predicates.pl")],
);
