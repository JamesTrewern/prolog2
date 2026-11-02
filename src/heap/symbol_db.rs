//! Per-program symbol database.
//!
//! All constant and variable symbols are interned here. Heap cells store
//! integer IDs rather than strings; this module provides the mapping in
//! both directions.
//!
//! A [`SymbolDB`] is owned by a [`ProgramHeap`](super::ProgramHeap) rather
//! than living in a global static, so two engines in one process keep
//! separate symbol spaces. Reach it through [`Heap::symbols`](super::Heap::symbols).

use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

/// Symbols interned at construction, at these fixed IDs.
///
/// `maths.rs` depends on the operator and function indices, and
/// `learners::specialise` on the `$inv_N` placeholder block: interning those
/// lazily would take the write lock once per learning candidate, which at
/// that volume is itself a bottleneck. The `$` prefix keeps them clear of the
/// `pred_N` constants the predicate definition table coins, which name real
/// predicates and would otherwise collide.
const KNOWN_SYMBOLS: &[&str] = &[
    "false",
    "true", // indices 0, 1
    "+",
    "-",
    "*",
    "/",
    "**", // indices 2-6
    "cos",
    "sin",
    "tan",
    "acos",
    "asin",
    "atan", // indices 7-12
    "log",
    "abs",
    "round",
    "sqrt",
    "to_degrees",
    "to_radians", // indices 13-18
];

/// How many `$inv_N` placeholder constants are preloaded.
///
/// These are not a budget for predicate invention. They stand in for the
/// predicate variables of a *single* candidate hypothesis while it is tested
/// against the negative examples, and are discarded with the rest of that
/// test's cells; the predicate definition table coins its own unbounded
/// `pred_N` constants for the predicates that are actually kept.
///
/// So the pool only has to cover the predicate variables of one candidate.
/// That is at most `max_clause - 1`, and `max_clause` is itself refused above
/// `MAX_PRED_DEFS` (16), making 15 the most that is reachable. The pool is
/// deliberately larger than that: it costs 64 small allocations once per
/// program, and leaves room for those two limits to rise.
pub(crate) const PRED_VAR_PLACEHOLDER_COUNT: usize = 64;

/// ID of the first `$inv_N` placeholder. The block runs for
/// [`PRED_VAR_PLACEHOLDER_COUNT`] consecutive IDs.
pub(crate) const PRED_VAR_PLACEHOLDER_BASE: usize = KNOWN_SYMBOLS.len();

/// Symbol table for one program.
///
/// Maps between string representations and numeric IDs so the heap can
/// work entirely with `usize` values. Constants, variables, and string
/// literals are stored separately.
///
/// Every method takes `&self`: the interior locks mean a symbol can be
/// interned through a shared reference, which is what lets a
/// [`QueryHeap`](super::QueryHeap) holding `&ProgramHeap` intern while
/// parsing a goal, and lets branches on worker threads read names.
///
/// Guards are never handed out, only taken and dropped inside a method, so
/// no caller can hold a read lock across a write and deadlock the
/// non-reentrant `RwLock`.
pub struct SymbolDB {
    /// Interned constants, and a reverse index so interning is not a scan.
    consts: RwLock<(Vec<Arc<str>>, HashMap<Arc<str>, usize>)>,
    var_symbol_map: RwLock<HashMap<(usize, usize), Arc<str>>>,
    strings: RwLock<Vec<Arc<str>>>,
}

impl Default for SymbolDB {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolDB {
    /// A table holding only the preloaded symbols.
    pub fn new() -> Self {
        let preloaded = KNOWN_SYMBOLS
            .iter()
            .map(|&symbol| Arc::<str>::from(symbol))
            .chain((0..PRED_VAR_PLACEHOLDER_COUNT).map(|i| Arc::<str>::from(format!("$inv_{i}").as_str())));

        let mut symbols = Vec::new();
        let mut index = HashMap::new();
        for symbol in preloaded {
            index.insert(symbol.clone(), symbols.len());
            symbols.push(symbol);
        }

        SymbolDB {
            consts: RwLock::new((symbols, index)),
            var_symbol_map: RwLock::new(HashMap::new()),
            strings: RwLock::new(Vec::new()),
        }
    }

    /// Intern a constant, returning its ID. Idempotent.
    pub fn set_const(&self, symbol: impl Into<Arc<str>>) -> usize {
        let symbol: Arc<str> = symbol.into();
        if let Some(&id) = self.consts.read().unwrap().1.get(&symbol) {
            return id;
        }
        let (symbols, index) = &mut *self.consts.write().unwrap();
        // Re-check: another thread may have interned it between the two locks.
        *index.entry(symbol.clone()).or_insert_with(|| {
            symbols.push(symbol);
            symbols.len() - 1
        })
    }

    pub fn get_const(&self, id: usize) -> Arc<str> {
        self.consts.read().unwrap().0[id].clone()
    }

    /// Record the source name of a variable.
    ///
    /// `key` identifies the variable within this program: a cell address for
    /// an `Arg` on the program heap, or a variable register ID paired with
    /// the owning query heap's ID.
    pub fn set_var(&self, symbol: impl Into<Arc<str>>, var: usize, heap_id: usize) {
        self.var_symbol_map
            .write()
            .unwrap()
            .insert((var, heap_id), symbol.into());
    }

    pub fn get_var(&self, var: usize, heap_id: usize) -> Option<Arc<str>> {
        self.var_symbol_map
            .read()
            .unwrap()
            .get(&(var, heap_id))
            .cloned()
    }

    pub fn get_string(&self, index: usize) -> Arc<str> {
        self.strings.read().unwrap()[index].clone()
    }

    pub fn set_string(&self, value: impl Into<Arc<str>>) -> usize {
        let mut strings = self.strings.write().unwrap();
        strings.push(value.into());
        strings.len() - 1
    }

    pub fn _see_var_map(&self) {
        for (k, v) in &*self.var_symbol_map.read().unwrap() {
            println!("{k:?}:\t{v}")
        }
    }
}
