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
mod varbind;

pub use heap::{Cell, Heap, Tag, CON_PTR, EMPTY_LIS, LIS};
pub use query_heap::{QueryHeap,HeapPoint};
pub use symbol_db::{known_symbol_id, SymbolDB};
pub use walk::{DualWalk, SubWalk, TermWalk, Walk};
pub use varbind::{VarBind,VarReg};

