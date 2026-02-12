use crate::heap::{heap::Tag, symbol_db::SymbolDB};
use fsize::fsize;
use std::{
    mem,
    ops::{Index, IndexMut, Range},
    sync::{
        atomic::{AtomicUsize, Ordering::Acquire},
        Arc,
    },
};

use super::heap::{Cell, Heap};

static HEAP_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);

pub struct QueryHeap {
    id: usize,
    pub(crate) cells: Vec<Cell>,
    prog_cells: Arc<Vec<Cell>>,
    //TODO handle branching query heap multi-threading
    root: Option<*const QueryHeap>,
}

impl QueryHeap {
    pub fn new(prog_cells: Arc<Vec<Cell>>, root: Option<*const QueryHeap>) -> QueryHeap {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        QueryHeap {
            id,
            cells: Vec::new(),
            prog_cells,
            root,
        }
    }

    pub fn branch(&self, count: usize) -> Vec<QueryHeap> {
        let mut branch_heap = Vec::with_capacity(count);
        for _ in 0..count {
            branch_heap.push(QueryHeap::new(self.prog_cells.clone(), Some(self)));
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
}

impl Heap for QueryHeap {
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

    /** Create String to represent cell, can be recursively used to format complex structures or list */
    fn term_string(&self, addr: usize) -> String {
        // println!("[{addr}]:{:?}", self[addr]);
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Con => SymbolDB::get_const(self[addr].1).to_string(),
            Tag::Func => self.func_string(addr),
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
            Tag::Stri => SymbolDB::get_string(self[addr].1).to_string(),
        }
    }
    
    fn truncate(&mut self, mut len: usize) {
        if len < self.prog_cells.len(){
            panic!("Can't truncate to prog cells")
        }
        len -= self.prog_cells.len();
        self.cells.resize(len, (Tag::Ref,0));
    }
}

impl Index<usize> for QueryHeap {
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

impl IndexMut<usize> for QueryHeap {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            panic!("Can't get mutable reference to program heap cell");
        } else {
            if let Some(root) = self.root {
                let root = unsafe { &*root };
                let root_heap_len = root.heap_len(); // prog_cells.len() + root.cells.len()
                if index < root_heap_len {
                    // Index is in root's query cells - deny mutable access
                    panic!("Can't get mutable reference to root heap cell");
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

impl Index<Range<usize>> for QueryHeap {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.prog_cells.len();

        if index.start < len && index.end < len {
            &self.prog_cells[index]
        } else if index.start >= len && self.root.is_none() {
            &self.cells[index.start - len..index.end - len]
        } else {
            panic!("Range splits static and mutable heap")
        }
    }
}
