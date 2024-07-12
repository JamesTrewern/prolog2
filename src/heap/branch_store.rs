use std::ops::{Index, IndexMut, Range};

use super::{heap::Heap, store::{Cell, Store}};

pub(crate) struct BranchStore<'a> {
    root_store: &'a Store<'a>,
    cells: Vec<Cell>
}

impl<'a> Heap for BranchStore<'a> {
    fn heap_push(&mut self, cell: Cell) {
        self.cells.push(cell);
    }

    fn heap_len(&self) -> usize {
        self.root_store.heap_len() + self.cells.len()
    }
}

impl<'a> Index<usize> for BranchStore<'a> {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.root_store.heap_len() {
            &self.root_store[index]
        } else {
            &self.cells[index - self.root_store.heap_len()]
        }
    }
}

impl<'a> IndexMut<usize> for BranchStore<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.root_store.heap_len() {
            panic!("Can't get mutable reference to root store cells");
        } else {
            &mut self.cells[index - self.root_store.heap_len()]
        }
    }
}

impl<'a> Index<Range<usize>> for BranchStore<'a>{
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.root_store.heap_len();
        if index.start < len && index.end < len{
            &self.root_store[index]
        }else if index.start >= len {
            &self.cells[index.start - len .. index.end - len]
        }else{
            panic!("Range splits static and mutable heap")
        }
    }
}