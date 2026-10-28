use crate::heap::SymbolDB;

use super::{
    Cell, Heap,
    Tag::*,
    TermWalk,
    VarBind::{self, *},
    VarReg, Walk,
};
use std::{
    collections::HashMap,
    ops::{Index, IndexMut, Range, RangeFrom},
    sync::atomic::{AtomicUsize, Ordering::Acquire},
};

static HEAP_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);
/// (Heap cells length, Variable registers length)
pub type HeapPoint = (usize, usize);

/// Working heap for proof search.
///
/// Wraps a shared read-only program heap (`&[Cell]`) and an
/// owned mutable cell buffer for query-time allocations. Supports
/// branching via an optional parent pointer for backtracking.
pub struct QueryHeap<'a> {
    pub(crate) id: usize,
    pub(crate) cells: Vec<Cell>,
    prog_cells: &'a [Cell],
    /// The cells of the heap this one was branched from, read-only.
    ///
    /// Addresses run `[prog_cells][root][cells]`, and `IndexMut` refuses
    /// anything below the end of `root`, so a branch can read everything its
    /// parent had allocated while writing only its own cells.
    ///
    /// Held as a plain slice rather than a pointer back to the parent heap:
    /// that is what makes a `QueryHeap` `Send`, so branches can be handed to
    /// different threads. The cost is that branches do not nest -- a branch
    /// of a branch would have two ancestors' cells to stitch together, and
    /// [`Self::branch`] rejects it.
    root: Option<&'a [Cell]>,
    pub(crate) var_regs: Vec<VarReg>, //Reference binding registers
}

impl<'a> QueryHeap<'a> {
    pub fn new(prog_cells: &'a [Cell], root: Option<&'a [Cell]>) -> QueryHeap<'a> {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        QueryHeap {
            id,
            cells: Vec::new(),
            prog_cells,
            root,
            var_regs: Vec::new(),
        }
    }

    /// `count` heaps that read this one's cells but write their own.
    ///
    /// Each gets a copy of the variable registers, so a branch can bind a
    /// variable this heap owns without the others, or this heap, seeing it.
    /// That is what makes the branches independent enough to run on separate
    /// threads, and it means nothing has to be undone afterwards: a branch is
    /// simply dropped.
    ///
    /// Borrows `self` for as long as the branches live, so the parent cannot
    /// allocate while they exist -- which is exactly the invariant their
    /// addresses depend on.
    pub fn branch<'b>(&'b self, count: usize) -> Vec<QueryHeap<'b>> {
        assert!(
            self.root.is_none(),
            "branches do not nest: this heap is already a branch"
        );
        (0..count)
            .map(|_| QueryHeap {
                id: HEAP_ID_COUNTER.fetch_add(1, Acquire),
                cells: Vec::new(),
                prog_cells: self.prog_cells,
                root: Some(&self.cells),
                var_regs: self.var_regs.clone(),
            })
            .collect()
    }

    /// Duplicate term from self, tracking variable identity
    /// via `ref_map`. Unbound Ref cells in `self` are mapped to fresh Ref
    /// cells in `self`; the same source Ref always maps to the same target Ref.
    /// Call with a shared `ref_map` across multiple terms to preserve variable
    /// sharing (e.g. across literals in a clause).
    /// Used to duplicate terms from immutable cells such as prog_cells or root_heap heap
    /// and place them in mutable cells.
    pub fn dup_term(&mut self, addr: usize, ref_map: &mut HashMap<usize, usize>) {
        let mut walk = TermWalk::new(addr);
        while let Some(cell) = walk.next_cell(self) {
            if cell.0 == Var {
                if let Some(&mapped) = ref_map.get(&addr) {
                    self.heap_push((Var, mapped));
                } else {
                    let new_var_id = self.set_var(None);
                    ref_map.insert(cell.1, new_var_id);
                }
            } else {
                self.heap_push(cell);
            }
        }
    }

    /// If true passed contrains, false if failed contraints
    pub fn check_constraints(&self, cons: &[usize]) -> bool {
        let derefs: Vec<VarBind> = cons.iter().map(|var_id| self.var_deref(*var_id)).collect();
        for i in 0..cons.len() {
            for j in (i + 1)..cons.len() {
                match (derefs[i], derefs[j]) {
                    (Addr(addr1), Addr(addr2)) if self.term_equal(addr1, addr2) => return false,
                    (v1, v2) if v1 == v2 => return false,
                    _ => (),
                }
            }
        }
        true
    }

    /// Get heap point to truncate back to later upon backtracking
    pub fn heap_point(&self) -> HeapPoint {
        (self.cells.len(), self.var_regs.len())
    }

    /// Free memory no longer needed upon back tracking
    pub fn truncate(&mut self, (cells_len, var_regs_len): HeapPoint) {
        self.cells.truncate(cells_len);
        self.var_regs.truncate(var_regs_len);
    }

    /// Create new variable register and return ID without creating cell
    pub fn new_var(&mut self, value: VarReg) -> usize {
        let var_id = self.var_regs.len();
        self.var_regs.push(value);
        var_id
    }

    pub fn _print_var_regs(&self) {
        println!("Var Regs");
        println!("------------");
        for (i, var_reg) in self.var_regs.iter().enumerate() {
            match var_reg.get_bind() {
                Some(bind) => println!("{i:3}: {bind:?}"),
                None => println!("{i:3}: UNBOUND"),
            }
        }
        println!("------------");
    }

    pub fn var_string(&self, var_id: usize) -> String {
        match SymbolDB::get_var(var_id, self.id) {
            Some(symbol) => symbol.to_string(),
            None => format!("Ref_{var_id}"),
        }
    }
}

impl Heap for QueryHeap<'_> {
    fn heap_push(&mut self, cell: Cell) -> usize {
        let i = self.heap_len();
        self.cells.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        self.prog_cells.len() + self.root.map_or(0, <[Cell]>::len) + self.cells.len()
    }

    fn get_id(&self, addr: usize) -> usize {
        if addr < self.prog_cells.len() {
            0
        } else {
            self.id
        }
    }

    fn prog_addr(&self, addr: usize) -> bool {
        addr >= self.prog_cells.len()
    }

    fn heap_last(&mut self) -> &mut Cell {
        self.cells.last_mut().unwrap()
    }

    #[inline(always)]
    fn var_deref(&self, mut var_id: usize) -> VarBind {
        loop {
            if self.var_regs[var_id].var() {
                var_id = self.var_regs[var_id].value()
            } else {
                if self.var_regs[var_id].bound() {
                    return Addr(self.var_regs[var_id].0);
                } else {
                    return VarId(var_id);
                }
            }
        }
    }

    /// Bind variable of var_id
    /// @var_id: variable id/bindinging index
    /// @value: value to set in binding
    /// @var: is binding to another variable id or an address
    fn bind(&mut self, var_id: usize, binding: VarBind) {
        self.var_regs[var_id].bind(binding);
    }

    fn unbind(&mut self, bound_vars: &[usize]) {
        for var_id in bound_vars {
            self.var_regs[*var_id].unbind();
        }
    }

    /// Add variable cell to heap
    /// If using existing var_id simple push new cell return var_id
    /// If creating new var push unbound to var bindings array and return new index (var_id)
    fn set_var(&mut self, var_id: Option<usize>) -> usize {
        //If no address provided set addr to current heap len
        let var_id = var_id.unwrap_or({
            //Create new var id
            let var_id = self.var_regs.len();
            self.var_regs.push(VarReg::UNBOUND);
            var_id
        });

        self.heap_push((Var, var_id));
        var_id
    }

    fn bound(&self, var_id: usize) -> Option<VarBind> {
        self.var_regs[var_id].get_bind()
    }
}

impl Index<usize> for QueryHeap<'_> {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.prog_cells.len() {
            return &self.prog_cells[index];
        }
        let offset = index - self.prog_cells.len();
        match self.root {
            // Parent's cells, then our own after them
            Some(root) if offset < root.len() => &root[offset],
            Some(root) => &self.cells[offset - root.len()],
            None => &self.cells[offset],
        }
    }
}

impl IndexMut<usize> for QueryHeap<'_> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            unreachable!(
                "IndexMut: attempted mutable access to program heap cell at index {index}"
            );
        }
        let offset = index - self.prog_cells.len();
        let root_len = self.root.map_or(0, <[Cell]>::len);
        if offset < root_len {
            unreachable!("IndexMut: attempted mutable access to parent heap cell at index {index}");
        }
        &mut self.cells[offset - root_len]
    }
}

impl Index<Range<usize>> for QueryHeap<'_> {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.prog_cells.len();

        if index.start < len && index.end <= len {
            &self.prog_cells[index]
        } else if index.start >= len && self.root.is_none() {
            &self.cells[index.start - len..index.end - len]
        } else {
            unreachable!("Index<Range>: range {index:?} spans the static program heap and mutable query cells")
        }
    }
}

impl Index<RangeFrom<usize>> for QueryHeap<'_> {
    type Output = [Cell];

    fn index(&self, mut index: RangeFrom<usize>) -> &Self::Output {
        assert!(
            index.start >= self.prog_cells.len(),
            "Can't Index with RangeFrom in program heap space"
        );
        assert!(
            self.root.is_none(),
            "Can't Index with RangeFrom on branched heap"
        );
        index.start -= self.prog_cells.len();
        &self.cells[index]
    }
}
