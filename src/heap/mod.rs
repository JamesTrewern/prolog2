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

pub use heap::{Binding, Cell, Heap, Tag, VarDeref, CON_PTR, EMPTY_LIS, LIS};
pub use query_heap::QueryHeap;
pub use symbol_db::{known_symbol_id, SymbolDB};
pub use walk::{DualWalk, TermWalk, Walk};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarBind {
    Unbound,
    Var(B7),
    Addr(B7),
}

const MAX_7: usize = (1 << 56) - 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct B7([u8; 7]);

impl Into<usize> for B7 {
    fn into(self) -> usize {
        let mut b = [0u8; 8];
        b[..7].copy_from_slice(&self.0);
        usize::from_le_bytes(b)
    }
}

impl From<usize> for B7 {
    fn from(value: usize) -> Self {
        let b = value.to_le_bytes();
        B7([b[0], b[1], b[2], b[3], b[4], b[5], b[6]])
    }
}

impl VarBind {
    pub fn bind(&mut self, value: usize, var: bool) {
        debug_assert!(!(*self == VarBind::Unbound), "Attempt to bind bound var");
        debug_assert!(value <= MAX_7, "value {value:#x} does not fit in 7 bytes");
        if var {
            *self = VarBind::Var(value.into());
        } else {
            *self = VarBind::Addr(value.into())
        }
    }

    pub fn unbind(&mut self) {
        debug_assert!(*self == VarBind::Unbound, "Attempt to unbind unbound var");
        *self = VarBind::Unbound
    }
}

impl From<(usize, bool)> for VarBind {
    fn from(value: (usize, bool)) -> Self {
        if value.1 {
            VarBind::Var(value.0.into())
        } else {
            VarBind::Addr(value.0.into())
        }
    }
}
