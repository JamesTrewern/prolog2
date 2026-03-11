/// Built-in maths predicates (`is/2`).
pub mod maths;
/// Built-in meta-predicates (`not/1`).
pub mod meta_predicates;

use crate::{
    heap::{query_heap::QueryHeap, symbol_db::SymbolDB},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

/// Return type for predicate functions.
///
/// A predicate either succeeds ([`PredReturn::True`]), fails ([`PredReturn::False`]),
/// or succeeds with variable bindings ([`PredReturn::Binding`]).
pub enum PredReturn {
    True,
    False,
    /// Success with a list of `(source_addr, target_addr)` bindings to apply on the heap.
    Binding(Vec<(usize, usize)>),
}

impl PredReturn {
    /// Convenience: convert a bool into [`PredReturn::True`] or [`PredReturn::False`].
    pub fn bool(value: bool) -> PredReturn {
        if value {
            PredReturn::True
        } else {
            PredReturn::False
        }
    }
}

/// Signature for a predicate function.
///
/// Arguments:
/// - `&mut QueryHeap` — the current proof's working heap
/// - `&mut Hypothesis` — the current learned hypothesis (may be extended)
/// - `usize` — heap address of the goal term being resolved
/// - `&PredicateTable` — the program's predicate table
/// - `Config` — engine configuration
pub type PredicateFunction = for<'a> fn(
    &mut QueryHeap<'a>,
    &mut Hypothesis,
    usize,
    &PredicateTable,
    Config,
) -> PredReturn;

/// A predicate module: a static slice of `(name, arity, function)` entries.
///
/// # Example
///
/// ```
/// use prolog2::predicate_modules::{PredicateModule, PredReturn};
///
/// static MY_MODULE: PredicateModule = &[
///     ("always_true", 0, |_heap, _hyp, _goal, _pt, _cfg| PredReturn::True),
/// ];
/// ```
pub type PredicateModule = &'static [(&'static str, usize, PredicateFunction)];

/// Register all entries from a predicate module into the predicate table.
pub fn load_predicate_module(
    predicate_table: &mut PredicateTable,
    predicate_module: &PredicateModule,
) {
    for (symbol, arity, pred_fn) in predicate_module.iter() {
        let _ = predicate_table.insert_predicate_function(
            (SymbolDB::set_const((*symbol).to_string()), *arity),
            *pred_fn,
        );
    }
}

/// Built-in maths predicates: `is/2` for arithmetic evaluation.
pub static MATHS: PredicateModule = &[
    ("is", 2, maths::is_pred),
];

/// Built-in meta-predicates: `not/1` (negation as failure).
pub static META_PREDICATES: PredicateModule = &[("not", 1, meta_predicates::not)];

/// Load all built-in predicate modules into the predicate table.
pub fn load_all_modules(predicate_table: &mut PredicateTable) {
    load_predicate_module(predicate_table, &MATHS);
    load_predicate_module(predicate_table, &META_PREDICATES);
}
