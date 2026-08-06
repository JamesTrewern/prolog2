use super::{
    Tag::*,
    TermWalk,
    VarBind::{self, *},
    VarReg, Walk,
};
use core::panic;
use std::{
    collections::HashMap,
    ops::{Index, IndexMut, Range, RangeFrom},
    sync::atomic::{AtomicUsize, Ordering::Acquire},
};

use super::heap::{Cell, Heap};

static HEAP_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// Working heap for proof search.
///
/// Wraps a shared read-only program heap (`&[Cell]`) and an
/// owned mutable cell buffer for query-time allocations. Supports
/// branching via an optional parent pointer for backtracking.
pub struct QueryHeap<'a> {
    id: usize,
    pub(crate) cells: Vec<Cell>,
    prog_cells: &'a [Cell],
    // TODO: handle branching query heap multi-threading
    root: Option<*const QueryHeap<'a>>,
    pub(crate) var_regs: Vec<VarReg>, //Reference binding registers
}

impl<'a> QueryHeap<'a> {
    pub fn new(prog_cells: &'a [Cell], root: Option<*const QueryHeap<'a>>) -> QueryHeap<'a> {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        let var_regs = if let Some(root) = root {
            unsafe { (&*root).var_regs.clone() }
        } else {
            Vec::new()
        };
        QueryHeap {
            id,
            cells: Vec::new(),
            prog_cells,
            root,
            var_regs,
        }
    }

    pub fn branch(&self, count: usize) -> Vec<QueryHeap<'a>> {
        let mut branch_heap = Vec::with_capacity(count);
        for _ in 0..count {
            branch_heap.push(QueryHeap::new(self.prog_cells, Some(self)));
        }
        branch_heap
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
            if cell.0 == Ref {
                if let Some(&mapped) = ref_map.get(&addr) {
                    self.heap_push((Ref, mapped));
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
        let mut i = 0;
        while i < cons.len() {
            let j = 0;
            while j < cons.len() {
                if i == j {
                    continue;
                }
                let _var_id1 = cons[i];
                let _var_id2 = cons[j];

                todo!("Effeciently compared vars to ensure they don't have same value");
                // follow var1 binding chain to value early return if hit var2_id
                // follow var2 binding chain to value early return if hit var1_id
                // if both unbound var compare id
                // if both address use heap.term_equal()
            }
            i += 1;
        }
        true
    }
}

impl Heap for QueryHeap<'_> {
    fn heap_push(&mut self, cell: Cell) -> usize {
        let i = self.heap_len();
        self.cells.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        match self.root {
            Some(root) => unsafe { &*root }.heap_len() + self.cells.len(),
            None => self.prog_cells.len() + self.cells.len(),
        }
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

    fn truncate(&mut self, mut len: usize) {
        debug_assert!(
            len >= self.prog_cells.len(),
            "truncate: target length {len} is below prog_cells boundary {}",
            self.prog_cells.len()
        );
        len -= self.prog_cells.len();
        self.cells.resize(len, (Ref, 0));
    }

    #[inline(always)]
    fn var_deref(&self, mut var_id: usize) -> VarBind {
        loop {
            if self.var_regs[var_id].var() {
                println!("{var_id}");
                var_id = self.var_regs[var_id].value()
            } else {
                if self.var_regs[var_id].bound() {
                    return Addr(self.var_regs[var_id].0);
                } else {
                    return Var(var_id);
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

        self.heap_push((Ref, var_id));
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
            &self.prog_cells[index]
        } else {
            if let Some(root) = self.root {
                let root = unsafe { &*root };
                if index < root.heap_len() {
                    // Index is in root's query cells
                    &root[index]
                } else {
                    // Index is in our own cells
                    &self.cells[index - root.heap_len()]
                }
            } else {
                &self.cells[index - self.prog_cells.len()]
            }
        }
    }
}

impl IndexMut<usize> for QueryHeap<'_> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            unreachable!(
                "IndexMut: attempted mutable access to program heap cell at index {index}"
            );
        } else {
            if let Some(root) = self.root {
                let root = unsafe { &*root };
                let root_heap_len = root.heap_len(); // prog_cells.len() + root.cells.len()
                if index < root_heap_len {
                    // Index is in root's query cells - deny mutable access
                    unreachable!(
                        "IndexMut: attempted mutable access to parent heap cell at index {index}"
                    );
                } else {
                    // Index is in our own cells
                    &mut self.cells[index - root_heap_len]
                }
            } else {
                &mut self.cells[index - self.prog_cells.len()]
            }
        }
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
            index.start > self.prog_cells.len(),
            "Can't Index with RangeFrom in program heap space"
        );
        assert!(
            self.root.is_none(),
            "Can't Index with RangeFrom on branched heap"
        );
        index.start += self.prog_cells.len();
        &self.cells[index]
    }
}
