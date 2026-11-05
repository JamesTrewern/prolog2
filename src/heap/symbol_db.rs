//! Per-program symbol database.
//!
//! Constants and string literals are interned here. Heap cells store integer
//! IDs rather than strings; this module provides the mapping in both
//! directions.
//!
//! Variable names are *not* here. A variable is identified by a register id
//! that means nothing outside the heap that created it, so each heap keeps
//! its own names -- see [`QueryHeap`](super::QueryHeap) for query variables
//! and [`ProgramHeap`](super::ProgramHeap) for clause `Arg`s.
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
/// `maths.rs` depends on the operator and function indices.
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

/// Symbol table for one program.
///
/// Maps between string representations and numeric IDs so the heap can work
/// entirely with `usize` values. Constants and string literals are stored
/// separately.
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
            .map(|&symbol| Arc::<str>::from(symbol));

        let mut symbols = Vec::new();
        let mut index = HashMap::new();
        for symbol in preloaded {
            index.insert(symbol.clone(), symbols.len());
            symbols.push(symbol);
        }

        SymbolDB {
            consts: RwLock::new((symbols, index)),
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

    pub fn get_string(&self, index: usize) -> Arc<str> {
        self.strings.read().unwrap()[index].clone()
    }

    pub fn set_string(&self, value: impl Into<Arc<str>>) -> usize {
        let mut strings = self.strings.write().unwrap();
        strings.push(value.into());
        strings.len() - 1
    }
}
