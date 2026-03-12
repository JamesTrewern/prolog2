//! Heap memory management for terms.
//!
//! The heap stores Prolog terms as flat arrays of [`Cell`](crate::heap::heap::Cell) values.
//! [`SymbolDB`](crate::heap::symbol_db::SymbolDB) provides the global mapping between string
//! symbols and numeric IDs. [`QueryHeap`](crate::heap::query_heap::QueryHeap) extends the static
//! program heap with mutable storage for proof search.

pub mod heap;
pub mod query_heap;
pub mod symbol_db;
