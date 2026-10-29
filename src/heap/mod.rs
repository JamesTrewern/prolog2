//! Heap memory management for terms.
//!
//! The heap stores Prolog terms as flat arrays of [`Cell`](crate::heap::Cell) values.
//! [`SymbolDB`](crate::heap::SymbolDB) provides the global mapping between string
//! symbols and numeric IDs. [`QueryHeap`](crate::heap::QueryHeap) extends the static
//! program heap with mutable storage for proof search.

mod argument_registers;
mod heap;
mod query_heap;
mod symbol_db;
mod varbind;
mod walk;

// Public: what a native predicate needs to read its goal and build a result.
// `HeapPoint` and `VarReg` are here because they appear in the signatures of
// public `QueryHeap` methods rather than because they are named directly.
pub use heap::{Cell, Heap, Tag, EMPTY_LIS, LIS};
pub use query_heap::{HeapPoint, QueryHeap};
pub use symbol_db::SymbolDB;
pub use varbind::{VarBind, VarReg};
pub use walk::{TermWalk, Walk};

// Internal: argument registers belong to clause resolution, and the paired
// walks to unification.
pub(crate) use argument_registers::ArgRegs;
pub(crate) use walk::{DualWalk, SubWalk};
