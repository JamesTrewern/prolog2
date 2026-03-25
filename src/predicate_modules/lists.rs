use crate::{
    heap::query_heap::QueryHeap,
    predicate_modules::PredicateModule,
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

use super::PredReturn;

/// Negation as failure: succeeds if the inner goal cannot be proven
pub fn length(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

/// Built-in list-predicates
pub static LISTS: PredicateModule = (
    &[("length", 2, length)],
    &[include_str!("../../builtins/lists.pl")],
);
