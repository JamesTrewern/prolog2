/// Built-in maths predicates (`is/2`).
pub mod maths;
/// Built-in meta-predicates (`not/1`).
pub mod meta_predicates;

pub mod lists;

pub use lists::LISTS;
pub use maths::MATHS;
pub use meta_predicates::META_PREDICATES;

use crate::{
    heap::{heap::Cell, query_heap::QueryHeap, symbol_db::SymbolDB},
    parser::{build_tree::TokenStream, execute_tree::execute_tree, tokeniser::tokenise},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

/// Return type for predicate functions.
///
/// A predicate either succeeds ([`PredReturn::True`]), fails ([`PredReturn::False`]),
/// or succeeds with heap mutations and/or new sub-goals ([`PredReturn::Success`]).
///
/// # Variants
///
/// The three variants cover the full range of outcomes a native predicate can produce:
///
/// - [`PredReturn::True`] — pure success with no heap side-effects; equivalent to
///   `Success(vec![], vec![])` but avoids allocating empty vecs for the common case.
/// - [`PredReturn::False`] — deterministic failure; the engine backtracks.
/// - [`PredReturn::Success`] — success with optional variable bindings and/or new
///   sub-goals to schedule. Either field may be empty:
///   - `Success(bindings, vec![])` — binds heap cells and succeeds (the former `Binding` case).
///   - `Success(vec![], goals)` — schedules new sub-goals without touching the heap.
///   - `Success(bindings, goals)` — both; the engine applies the bindings *then* resolves
///     the additional goals as if they had been in the clause body.
///
/// > **Note:** sub-goal scheduling via `Success(_, goals)` is not yet implemented in the
/// > resolution engine. Returning a non-empty `goals` vec will currently panic with
/// > `todo!()`. The variant is present so the API does not need to change once the
/// > feature is added.
pub enum PredReturn {
    True,
    False,
    /// Success with variable bindings to apply and new sub-goals to resolve.
    ///
    /// - First field: `(source_addr, target_addr)` heap bindings.
    /// - Second field: heap addresses of additional sub-goals to schedule (may be empty).
    Success(Vec<(usize, usize)>, Vec<usize>),
}

impl From<bool> for PredReturn {
    fn from(value: bool) -> Self {
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
pub type PredicateFunction =
    for<'a> fn(&mut QueryHeap<'a>, &mut Hypothesis, usize, &PredicateTable, Config) -> PredReturn;

/// A predicate module: a tuple of native predicate entries and built-in Prolog source code.
///
/// The two components let you extend the engine in two complementary ways:
///
/// 1. **Native predicates** — a static slice of `(name, arity, function)` triples wired
///    directly into the engine. Use these for anything that needs to inspect or mutate heap
///    memory, perform I/O, or call into Rust logic that cannot be expressed in Prolog.
///    Each function returns a [`PredReturn`] describing whether the predicate succeeded,
///    failed, or succeeded with variable bindings.
///
/// 2. **Prolog source** — a static slice of `&str` source snippets (typically embedded at
///    compile time with `include_str!`). These are parsed and loaded as ordinary clauses
///    when the module is registered, so they can call each other or any native predicates
///    in the module.
///
/// Either slice may be empty if the module only uses one mechanism.
///
/// # Example
///
/// ```
/// use prolog2::predicate_modules::{PredicateModule, PredReturn};
///
/// static MY_MODULE: PredicateModule = (&[
///     ("always_true", 0, |_heap, _hyp, _goal, _pt, _cfg| PredReturn::True),
/// ], &[]);
/// ```
pub type PredicateModule = (
    &'static [(&'static str, usize, PredicateFunction)],
    &'static [&'static str],
);

/// Register all entries from a predicate module into the predicate table.
pub fn load_predicate_module(
    predicate_table: &mut PredicateTable,
    heap: &mut Vec<Cell>,
    predicate_module: &PredicateModule,
) {
    for (symbol, arity, pred_fn) in predicate_module.0.iter() {
        let _ = predicate_table.insert_predicate_function(
            (SymbolDB::set_const((*symbol).to_string()), *arity),
            *pred_fn,
        );
    }
    for &file in predicate_module.1.iter() {
        let syntax_tree = TokenStream::new(tokenise(&file).unwrap())
            .parse_all()
            .unwrap();

        execute_tree(syntax_tree, heap, predicate_table);
    }
}

/// Load all built-in predicate modules into the predicate table.
pub fn load_all_modules(predicate_table: &mut PredicateTable, heap: &mut Vec<Cell>) {
    load_predicate_module(predicate_table, heap, &MATHS);
    load_predicate_module(predicate_table, heap, &META_PREDICATES);
    load_predicate_module(predicate_table, heap, &LISTS);
}

pub static DEFAULT_MODULES: &[PredicateModule] = &[MATHS, META_PREDICATES, LISTS];
