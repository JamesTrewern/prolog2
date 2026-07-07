use crate::heap::{TermWalk, LIS, Tag};
use std::{
    collections::HashMap,
    ops::{Index, IndexMut, Range},
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
}

impl<'a> QueryHeap<'a> {
    pub fn new(prog_cells: &'a [Cell], root: Option<*const QueryHeap<'a>>) -> QueryHeap<'a> {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        QueryHeap {
            id,
            cells: Vec::new(),
            prog_cells,
            root,
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
        let mut addr_stack = TermWalk::new(addr);
        loop {
            let addr = if let Some(addr) = addr_stack.next_addr(){
                if let Some(deref_addr) = self.is_deref(addr) {
                    addr_stack.add_frame(deref_addr);
                    deref_addr
                }else{
                    addr
                }
            }else{
                return;
            };
            match self[addr] {
                LIS => {
                    self.heap_push(LIS);
                    addr_stack.increment_cells_left(2);
                }
                cell @ (Tag::Comp | Tag::Tup | Tag::Set, len) => {
                    self.heap_push(cell);
                    addr_stack.increment_cells_left(len);
                }
                (Tag::Ref, addr) => {
                    if let Some(&mapped) = ref_map.get(&addr) {
                        self.heap_push((Tag::Ref, mapped));
                    } else {
                        let new_addr = self.heap_len();
                        self.heap_push((Tag::Ref, new_addr));
                        ref_map.insert(addr, new_addr);
                    }
                }
                cell => _ = self.heap_push(cell),
            }
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
        self.cells.resize(len, (Tag::Ref, 0));
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

        if index.start < len && index.end < len {
            &self.prog_cells[index]
        } else if index.start >= len && self.root.is_none() {
            &self.cells[index.start - len..index.end - len]
        } else {
            unreachable!("Index<Range>: range {index:?} spans the static program heap and mutable query cells")
        }
    }
}
