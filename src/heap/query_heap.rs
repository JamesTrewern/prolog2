use crate::heap::{heap::Tag, symbol_db::SymbolDB};
use fsize::fsize;
use std::{
    collections::HashMap,
    mem,
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

    fn get_symbol_db_id(&self, addr: usize) -> usize {
        if addr < self.prog_cells.len() {
            0
        } else {
            self.id
        }
    }

    /// Duplicate term from self, tracking variable identity
    /// via `ref_map`. Unbound Ref cells in `self` are mapped to fresh Ref
    /// cells in `self`; the same source Ref always maps to the same target Ref.
    /// Call with a shared `ref_map` across multiple terms to preserve variable
    /// sharing (e.g. across literals in a clause).
    /// Used to duplicate terms from immutable cells such as prog_cells or root_heap heap
    /// and place them in mutable cells.
    pub fn dup_term(
        &mut self,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> usize {
        let addr = self.deref_addr(addr);
        match self[addr] {
            (Tag::Str, pointer) => {
                let new_ptr = self.dup_term( pointer, ref_map);
                self.heap_push((Tag::Str, new_ptr));
                self.heap_len() - 1
            }
            (Tag::Comp | Tag::Tup | Tag::Set, length) => {
                // Pre-pass: recursively copy complex sub-terms
                let mut pre: Vec<Option<Cell>> = Vec::with_capacity(length);
                for i in 1..=length {
                    pre.push(self.dup_complex( addr + i, ref_map));
                }
                // Lay down structure header + sub-terms
                let h = self.heap_len();
                self.heap_push((self[addr].0, length));
                for (i, pre_cell) in pre.into_iter().enumerate() {
                    match pre_cell {
                        Some(cell) => {
                            self.heap_push(cell);
                        }
                        None => self.dup_simple( addr + 1 + i, ref_map),
                    }
                }
                h
            }
            (Tag::Lis, pointer) => {
                let head = self.dup_complex( pointer, ref_map);
                let tail = self.dup_complex( pointer + 1, ref_map);
                let h = self.heap_len();
                match head {
                    Some(cell) => {
                        self.heap_push(cell);
                    }
                    None => self.dup_simple( pointer, ref_map),
                }
                match tail {
                    Some(cell) => {
                        self.heap_push(cell);
                    }
                    None => self.dup_simple(pointer + 1, ref_map),
                }
                h
            }
            (Tag::Ref, r) if r == addr => {
                // Unbound ref — use or create mapping
                if let Some(&mapped) = ref_map.get(&addr) {
                    mapped
                } else {
                    let new_addr = self.heap_len();
                    self.heap_push((Tag::Ref, new_addr));
                    ref_map.insert(addr, new_addr);
                    new_addr
                }
            }
            (Tag::Arg | Tag::Con | Tag::Int | Tag::Flt | Tag::Stri | Tag::ELis, _) => {
                self.heap_push(self[addr]);
                self.heap_len() - 1
            }
            (tag, val) => unreachable!("dup_term_with_ref_map: unhandled cell ({tag:?}, {val})"),
        }
    }

    /// Pre-pass helper for dup_term_with_ref_map: recursively copy complex
    /// sub-terms and return the Cell to later insert, or None for simple cells.
    fn dup_complex(
        &mut self,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> Option<Cell> {
        let addr = self.deref_addr(addr);
        match self[addr] {
            (Tag::Comp | Tag::Tup | Tag::Set, _) => {
                Some((Tag::Str, self.dup_term( addr, ref_map)))
            }
            (Tag::Str, ptr) => Some((Tag::Str, self.dup_term( ptr, ref_map))),
            (Tag::Lis, _) => Some((Tag::Lis, self.dup_term( addr, ref_map))),
            _ => None,
        }
    }

    /// Post-pass helper for dup_term_with_ref_map: push a simple cell,
    /// handling Ref identity via ref_map.
    fn dup_simple(
        &mut self,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) {
        let addr = self.deref_addr(addr);
        match self[addr] {
            (Tag::Ref, r) if r == addr => {
                if let Some(&mapped) = ref_map.get(&addr) {
                    self.heap_push((Tag::Ref, mapped));
                } else {
                    let new_addr = self.heap_len();
                    self.heap_push((Tag::Ref, new_addr));
                    ref_map.insert(addr, new_addr);
                }
            }
            cell => {
                self.heap_push(cell);
            }
        }
    }

}

impl Heap for QueryHeap<'_> {
    #[inline(always)]
    fn deref_addr(&self, mut addr: usize) -> usize {
        loop {
            let cell = self[addr];
            match cell {
                (Tag::Ref, pointer) if addr == pointer => return pointer,
                (Tag::Ref, pointer) => addr = pointer,
                _ => return addr,
            }
        }
    }

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

    fn get_id(&self) -> usize {
        self.id
    }

    fn prog_addr(&self, addr: usize) -> bool {
        addr >= self.prog_cells.len()
    }

    fn heap_last(&mut self) -> &mut Cell {
        self.cells.last_mut().unwrap()
    }

    /** Create String to represent cell, can be recursively used to format complex structures or list */
    fn term_string(&self, addr: usize) -> String {
        // println!("[{addr}]:{:?}", self[addr]);
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Con => SymbolDB::get_const(self[addr].1).to_string(),
            Tag::Comp => self.func_string(addr),
            Tag::Lis => self.list_string(addr),
            Tag::ELis => "[]".into(),
            Tag::Arg => match SymbolDB::get_var(addr, self.get_symbol_db_id(addr)) {
                Some(symbol) => symbol.to_string(),
                None => format!("Arg_{}", self[addr].1),
            },
            Tag::Ref => match SymbolDB::get_var(self.deref_addr(addr), self.get_symbol_db_id(addr))
                .to_owned()
            {
                Some(symbol) => symbol.to_string(),
                None => format!("Ref_{}", self[addr].1),
            },
            Tag::Int => {
                let value: isize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Flt => {
                let value: fsize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Tup => self.tuple_string(addr),
            Tag::Set => self.set_string(addr),
            Tag::Str => self.term_string(self[addr].1),
            Tag::Stri => format!("\"{}\"", SymbolDB::get_string(self[addr].1)),
            Tag::AVar => "_".into(),
        }
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
