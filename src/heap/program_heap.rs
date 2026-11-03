//! The static program heap: clause cells plus the program's symbol table.

use std::{
    collections::HashMap,
    ops::{Deref, Index, IndexMut, Range, RangeFrom},
    sync::Arc,
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
///
/// Variable names are split between the two. Clause `Arg`s live here, named
/// by cell address at parse time. Query variables are named by their owning
/// query heap, because a register id means nothing outside the heap that
/// issued it -- which is why neither needs a heap identifier to disambiguate
/// it.
pub struct ProgramHeap {
    cells: Vec<Cell>,
    /// Argument registers needed by the widest clause compiled into this
    /// heap -- the number of distinct variables in it, matching
    /// [`Clause::max_arg_id`](crate::program::Clause).
    ///
    /// This bounds the argument registers any proof over this program can
    /// touch, so a [`QueryHeap`](super::QueryHeap) sizes its argument window
    /// from it rather than reserving a fixed maximum.
    ///
    /// It only grows when source is compiled. Instantiating a meta clause can
    /// drop arguments but never add them -- `build_arg` re-pushes `(Arg, id)`
    /// with the id unchanged, substitutes a bound value, or mints a
    /// *variable* -- so the clauses the learner installs at run time cannot
    /// raise it. That is what makes the window safe to fix at query time, and
    /// what the assertion in [`Self::heap_push`] checks.
    max_arg: usize,
    symbols: SymbolDB,
    /// Source names of clause variables, keyed by the address of the `Arg`
    /// cell.
    ///
    /// Keyed by address rather than by `Arg` id because those ids are
    /// clause-local: `Arg 0` means a different variable in every clause, so
    /// only the cell's position identifies it within the program.
    arg_names: HashMap<usize, Arc<str>>,
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
            max_arg: 0,
            symbols: SymbolDB::new(),
            arg_names: HashMap::new(),
        }
    }

    /// Build a program heap over existing cells. Mostly useful in tests.
    pub fn from_cells(cells: Vec<Cell>) -> Self {
        ProgramHeap {
            cells,
            ..Self::new()
        }
    }

    pub(crate) fn cells(&self) -> &[Cell] {
        &self.cells
    }

    /// Argument registers needed by the widest clause in this program.
    pub fn max_arg(&self) -> usize {
        self.max_arg
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

    fn arg_name(&self, addr: usize) -> Option<Arc<str>> {
        self.arg_names.get(&addr).cloned()
    }

    fn set_arg_name(&mut self, addr: usize, symbol: Arc<str>) {
        self.arg_names.insert(addr, symbol);
    }

    fn heap_push(&mut self, cell: Cell) -> usize {
        debug_assert!(
            cell.0 != crate::heap::Tag::Arg || cell.1 < self.max_arg,
            "Arg {} pushed into program space but the program's widest clause needs only \
             {} argument registers. A query heap's argument window is sized from that \
             figure, so raising it here would leave live heaps undersized.",
            cell.1,
            self.max_arg,
        );
        self.cells.push(cell);
        self.cells.len() - 1
    }

    fn observe_arg_count(&mut self, count: usize) {
        self.max_arg = self.max_arg.max(count);
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
