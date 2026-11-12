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
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock,
    },
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

/// Start of an invented symbol's name; its number follows.
const INVENTED_PREFIX: &str = "pred_";

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
    /// Id the next invented symbol takes, or 0 before the first is invented.
    ///
    /// 0 can stand for "none" because the preloaded symbols hold the low ids.
    /// Invented ids start at the number of interned constants, so no
    /// constant may be interned after the first invention.
    next_inv: AtomicUsize,
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
            next_inv: AtomicUsize::new(0),
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
            debug_assert_eq!(
                self.next_inv.load(Ordering::Relaxed),
                0,
                "interning {symbol:?} after a symbol was invented would reuse an invented id"
            );
            symbols.push(symbol);
            symbols.len() - 1
        })
    }

    /// The id of a new invented symbol.
    ///
    /// An invented symbol has no stored name: its id is past the interned
    /// constants, and [`Self::get_const`] writes its name out on request.
    pub fn next_inv(&self) -> usize {
        let mut current = self.next_inv.load(Ordering::Relaxed);
        loop {
            let id = match current {
                0 => self.consts.read().unwrap().0.len(),
                id => id,
            };
            match self.next_inv.compare_exchange_weak(
                current,
                id + 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return id,
                Err(changed) => current = changed,
            }
        }
    }

    pub fn get_const(&self, id: usize) -> Arc<str> {
        let symbols = &self.consts.read().unwrap().0;
        match symbols.get(id) {
            Some(symbol) => symbol.clone(),
            None => format!("{INVENTED_PREFIX}{}", id - symbols.len()).into(),
        }
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

#[cfg(test)]
mod tests {
    use super::SymbolDB;

    #[test]
    fn invented_ids_follow_the_interned_constants() {
        let symbols = SymbolDB::new();
        let last = symbols.set_const("invented_ids_last_constant");

        assert_eq!(symbols.next_inv(), last + 1);
        assert_eq!(symbols.next_inv(), last + 2);
        assert_eq!(symbols.next_inv(), last + 3);
    }

    #[test]
    fn an_invented_symbol_is_named_by_its_number() {
        let symbols = SymbolDB::new();
        let first = symbols.next_inv();
        let second = symbols.next_inv();

        assert_eq!(&*symbols.get_const(first), "pred_0");
        assert_eq!(&*symbols.get_const(second), "pred_1");
    }

    #[test]
    fn an_interned_constant_can_still_be_looked_up_after_inventing() {
        let symbols = SymbolDB::new();
        let id = symbols.set_const("looked_up_after_inventing");
        symbols.next_inv();

        assert_eq!(symbols.set_const("looked_up_after_inventing"), id);
        assert_eq!(&*symbols.get_const(id), "looked_up_after_inventing");
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "would reuse an invented id")]
    fn interning_a_new_constant_after_inventing_is_refused() {
        let symbols = SymbolDB::new();
        symbols.next_inv();
        symbols.set_const("interned_after_inventing");
    }
}
