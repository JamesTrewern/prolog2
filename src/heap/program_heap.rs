//! The static program heap: clause cells plus the program's symbol table.

use std::{
    ops::{Deref, Index, IndexMut, Range, RangeFrom},
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

use super::{Cell, Heap, SymbolDB, VarBind};

/// Cells for the loaded program, and the [`SymbolDB`] they are interpreted
/// against.
///
/// The two belong together: a `Con` cell's value means nothing without the
/// table that maps it back to a name, so a program heap and its symbols have
/// the same lifetime and the same owner. Keeping the table here rather than in
/// a global static is what lets two engines coexist in one process -- symbol
/// IDs, string literal indices and query heap IDs are all private to one
/// program.
///
/// A [`QueryHeap`](super::QueryHeap) borrows this immutably for its whole
/// life and reaches the table through [`Heap::symbols`]. That the symbol
/// methods take `&self` is therefore load-bearing: a goal being parsed into a
/// query heap must be able to intern constants with only a shared reference
/// to the program.
pub struct ProgramHeap {
    cells: Vec<Cell>,
    symbols: SymbolDB,
    /// Next ID to hand to a query heap borrowing this program.
    ///
    /// Local to one program, so IDs stay dense and two engines cannot collide
    /// in the variable-name map. Starts at 1: ID 0 means "a program heap
    /// address", which [`Heap::get_id`] returns for cells below
    /// `cells.len()`.
    ///
    /// Atomic rather than a `Cell`, because IDs are handed out through the
    /// shared `&ProgramHeap` that query heaps and their branches hold, and
    /// because a non-`Sync` field here would make `&ProgramHeap` non-`Send`
    /// and so stop branches crossing threads.
    next_heap_id: AtomicUsize,
}

impl Default for ProgramHeap {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramHeap {
    /// An empty program heap with a freshly preloaded symbol table.
    pub fn new() -> Self {
        ProgramHeap {
            cells: Vec::new(),
            symbols: SymbolDB::new(),
            next_heap_id: AtomicUsize::new(1),
        }
    }

    /// Build a program heap over existing cells. Mostly useful in tests.
    pub fn from_cells(cells: Vec<Cell>) -> Self {
        ProgramHeap {
            cells,
            ..Self::new()
        }
    }

    /// Hand out the next query heap ID.
    pub(crate) fn next_heap_id(&self) -> usize {
        self.next_heap_id.fetch_add(1, Relaxed)
    }

    pub(crate) fn cells(&self) -> &[Cell] {
        &self.cells
    }

    /// Append cells wholesale. Callers relocating addresses must account for
    /// the length before the call.
    pub(crate) fn extend_from_slice(&mut self, cells: &[Cell]) {
        self.cells.extend_from_slice(cells);
    }
}

/// Read-only slice access, so `len`, `iter` and friends work as they did when
/// the program heap was a bare `Vec<Cell>`.
impl Deref for ProgramHeap {
    type Target = [Cell];

    fn deref(&self) -> &[Cell] {
        &self.cells
    }
}

impl Heap for ProgramHeap {
    fn symbols(&self) -> &SymbolDB {
        &self.symbols
    }

    fn heap_push(&mut self, cell: Cell) -> usize {
        self.cells.push(cell);
        self.cells.len() - 1
    }

    fn heap_len(&self) -> usize {
        self.cells.len()
    }

    fn heap_last(&mut self) -> &mut Cell {
        self.cells.last_mut().unwrap()
    }

    fn set_var(&mut self, _: Option<usize>) -> usize {
        unreachable!("Shouldn't set var in program heap");
    }

    fn bound(&self, _var_id: usize) -> Option<VarBind> {
        unreachable!("Should not consult program heap for variable binding")
    }

    fn var_deref(&self, _: usize) -> VarBind {
        unreachable!("no vars to deref in program heap")
    }

    fn bind(&mut self, _: usize, _: VarBind) {
        unreachable!("Should not attempt to bind in program heap")
    }

    fn unbind(&mut self, _: &[usize]) {
        unreachable!("Should not attempt to unbind in program heap")
    }
}

impl Index<usize> for ProgramHeap {
    type Output = Cell;

    fn index(&self, index: usize) -> &Cell {
        &self.cells[index]
    }
}

impl IndexMut<usize> for ProgramHeap {
    fn index_mut(&mut self, index: usize) -> &mut Cell {
        &mut self.cells[index]
    }
}

impl Index<Range<usize>> for ProgramHeap {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &[Cell] {
        &self.cells[index]
    }
}

impl Index<RangeFrom<usize>> for ProgramHeap {
    type Output = [Cell];

    fn index(&self, index: RangeFrom<usize>) -> &[Cell] {
        &self.cells[index]
    }
}
