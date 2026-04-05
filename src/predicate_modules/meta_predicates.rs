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
    //Extract inner negated goal
    let inner_goal = resolve(heap, goal_arg(heap, goal, 0));

    // Create a config with learning disabled
    let mut inner_config = config;
    inner_config.max_clause = 0; // Disable learning by not allowing new clauses

    // Clone the current hypothesis so the inner proof can use the learned clauses
    let hypothesis_clone = hypothesis.clone();
    let mut inner_proof = Proof::with_hypothesis(heap, &[inner_goal], hypothesis_clone);

    if config.debug {
        eprintln!(
            "[NEGATE] {} with {} hypothesis clauses",
            heap.term_string(inner_goal),
            inner_proof.hypothesis.len()
        );
    }

    // Try to prove the inner goal with the current hypothesis
    // If it succeeds, not/1 fails (the hypothesis entails something it shouldn't)
    // If it fails, not/1 succeeds (the hypothesis correctly doesn't entail this)
    if inner_proof.prove(heap,predicate_table, inner_config) {
        if config.debug {
            eprintln!(
                "[FAILED_TO_NEGATE] {}",
                heap.term_string(inner_goal)
            );
        }
        PredReturn::False
    } else {
        if config.debug {
            eprintln!(
                "[NEGATED_THROUGH_FAILURE] {}",
                heap.term_string(inner_goal)
            );
        }
        PredReturn::True
    }
}

///find_all(+Template,:Goal,-Bag)
pub fn findall(
    _heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    _goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    todo!()
}

/// Built-in meta-predicates: `not/1` (negation as failure).
pub static META_PREDICATES: PredicateModule = (
    &[
        ("not", 1, not),
        // ("findall", 3, findall),
    ],
    &[include_str!("../../builtins/meta_predicates.pl")],
);
