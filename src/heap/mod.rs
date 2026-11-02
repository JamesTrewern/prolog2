//! Heap memory management for terms.
//!
//! The heap stores Prolog terms as flat arrays of [`Cell`](crate::heap::Cell) values.
//! [`ProgramHeap`](crate::heap::ProgramHeap) holds the loaded program's cells
//! together with the [`SymbolDB`](crate::heap::SymbolDB) mapping between string
//! symbols and the numeric IDs those cells store, and
//! [`QueryHeap`](crate::heap::QueryHeap) borrows a program heap and extends it with
//! mutable storage for proof search. Any heap reaches its symbols through
//! [`Heap::symbols`](crate::heap::Heap::symbols), so naming a term never needs the
//! table passed alongside it.

mod argument_registers;
mod heap;
mod program_heap;
mod query_heap;
mod symbol_db;
mod varbind;
mod walk;

// Public: what a native predicate needs to read its goal and build a result.
// `HeapPoint` and `VarReg` are here because they appear in the signatures of
// public `QueryHeap` methods rather than because they are named directly.
pub use heap::{Cell, Heap, Tag, EMPTY_LIS, LIS};
pub use program_heap::ProgramHeap;
pub use query_heap::{HeapPoint, QueryHeap};
pub use symbol_db::SymbolDB;
pub(crate) use symbol_db::{PRED_VAR_PLACEHOLDER_BASE, PRED_VAR_PLACEHOLDER_COUNT};
pub use varbind::{VarBind, VarReg};
pub use walk::{TermWalk, Walk};

// Internal: argument registers belong to clause resolution, and the paired
// walks to unification.
pub(crate) use argument_registers::ArgRegs;
pub(crate) use walk::{DualWalk, SubWalk};

/// The program heap tests build against when they do not need one of their own.
///
/// A singleton, and deliberately so: a constant interned through one call has
/// to be readable through any other, which a fresh heap per call would break.
/// It holds no cells, so query-heap addresses still start at zero, and every
/// [`QueryHeap`] built on it still gets a distinct ID.
///
/// That the whole test binary can share this safely -- tests run on several
/// threads and intern concurrently -- is the property the per-program
/// [`SymbolDB`] exists to provide.
#[cfg(test)]
pub(crate) fn test_prog() -> &'static ProgramHeap {
    static PROG: std::sync::OnceLock<ProgramHeap> = std::sync::OnceLock::new();
    PROG.get_or_init(ProgramHeap::new)
}
