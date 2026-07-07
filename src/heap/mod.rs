//! Heap memory management for terms.
//!
//! The heap stores Prolog terms as flat arrays of [`Cell`](crate::heap::Cell) values.
//! [`SymbolDB`](crate::heap::SymbolDB) provides the global mapping between string
//! symbols and numeric IDs. [`QueryHeap`](crate::heap::QueryHeap) extends the static
//! program heap with mutable storage for proof search.

mod heap;
mod query_heap;
mod symbol_db;
mod walk;

pub use heap::{Heap,Cell,Tag,LIS,EMPTY_LIS,CON_PTR};
pub use query_heap::QueryHeap;
pub use walk::{TermWalk,DualWalk};
pub use symbol_db::{SymbolDB,known_symbol_id};