use super::heap::{Cell, Heap, Tag, CON_PTR};
use manual_rwlock::ReadGaurd;
use std::ops::{Index, IndexMut, Range};

const HEAP_SIZE: usize = 1024;
#[derive(Clone)]
pub(crate) struct QueryHeap<'a> {
    pub read_cells: ReadGaurd<'a, Vec<Cell>>,
    pub cells: Vec<Cell>,
}

impl<'a> Heap for QueryHeap<'a> {
    fn heap_push(&mut self, cell: Cell) {
        self.cells.push(cell)
    }

    fn heap_len(&self) -> usize {
        self.read_cells.len() + self.cells.len()
    }
}

impl<'a> QueryHeap<'a> {
    pub fn new(prog_cells: ReadGaurd<Vec<Cell>>) -> QueryHeap {
        QueryHeap {
            cells: Vec::with_capacity(HEAP_SIZE),
            read_cells: prog_cells,
        }
    }

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    pub fn bind(&mut self, binding: &[(usize, usize)]) {
        for (src, target) in binding {
            // println!("{}", self.term_string(*src));
            let pointer = &mut self[*src].1;
            if *pointer != *src {
                panic!("Tried to reset bound ref: {} \n Binding: {binding:?}", src)
            }
            *pointer = *target;
        }
    }

    /** Reset Ref cells affected by binding to self references
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    pub fn unbind(&mut self, binding: &[(usize, usize)]) {
        for (src, _target) in binding {
            if let (Tag::Ref, pointer) = &mut self[*src] {
                *pointer = *src;
            }
        }
    }
}

impl<'a> Index<usize> for QueryHeap<'a> {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.read_cells.len() {
            &self.read_cells[index]
        } else {
            &self.cells[index - self.read_cells.len()]
        }
    }
}

impl<'a> IndexMut<usize> for QueryHeap<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.read_cells.len() {
            panic!("Can't get mutable reference to program heap cell");
        } else {
            &mut self.cells[index - self.read_cells.len()]
        }
    }
}

impl<'a> Index<Range<usize>> for QueryHeap<'a> {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.read_cells.len();
        if index.start < len && index.end < len {
            &self.read_cells[index]
        } else if index.start >= len {
            &self.cells[index.start - len..index.end - len]
        } else {
            panic!("Range splits static and mutable heap")
        }
    }
}

pub(crate) struct ListIter<'a> {
    pub store: &'a QueryHeap<'a>,
    pub index: usize,
}

impl<'a> Iterator for ListIter<'a> {
    type Item = (Cell, bool);

    fn next(&mut self) -> Option<Self::Item> {
        if let (Tag::Lis, pointer) = self.store[self.index] {
            if pointer == CON_PTR {
                None
            } else {
                self.index = pointer + 1;
                Some((self.store[pointer], false))
            }
        } else {
            Some((self.store[self.index], true))
        }
    }
}
