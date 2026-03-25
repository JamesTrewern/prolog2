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
/// or succeeds with variable bindings ([`PredReturn::Binding`]).
pub enum PredReturn {
    True,
    False,
    /// Success with a list of `(source_addr, target_addr)` bindings to apply on the heap.
    Binding(Vec<(usize, usize)>),
    Goal(Vec<(usize, usize)>, Vec<usize>),
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
/// - The first element is a static slice of `(name, arity, function)` entries for native predicates.
/// - The second element is a static slice of Prolog source strings, typically embedded at compile
///   time via `include_str!` from the `builtins/` directory.
///
/// # Example
///
/// ```
/// use prolog2::predicate_modules::{PredicateModule, PredReturn};
///
/// static MY_MODULE: PredicateModule = (&[
///     ("always_true", 0, |_heap, _hyp, _goal, _pt, _cfg| PredReturn::True),
/// ], &[include_str!("../../builtins/my_module.pl")]);
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
