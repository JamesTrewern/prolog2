use std::{ops::{Index, IndexMut, Range}, sync::{atomic::{AtomicUsize,Ordering::Acquire}, Arc, }};

use super::heap::{Cell, Heap};

static HEAP_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);

pub struct QueryHeap {
    id: usize,
    pub(crate) cells: Vec<Cell>,
    prog_cells: Arc<Vec<Cell>>,
    //TODO handle branching query heap multi-threading
    root: Option<*const QueryHeap>,
}

impl  QueryHeap  {
    pub fn new(
        prog_cells: Arc<Vec<Cell>>,
        root: Option<*const QueryHeap>
    ) -> QueryHeap  {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        QueryHeap {
            id,
            cells: Vec::new(),
            prog_cells,
            root,
        }
    }

    pub fn branch(&self, count: usize) -> Vec<QueryHeap>{
        let mut branch_heap = Vec::with_capacity(count);
        for _ in 0..count{
            branch_heap.push(QueryHeap::new(self.prog_cells.clone(), Some(self)));
        }
        branch_heap
    }
}

impl  Heap for QueryHeap  {
    fn heap_push(&mut self, cell: Cell) -> usize{
        let i = self.heap_len();
        self.cells.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        match self.root{
            Some(root) => self.prog_cells.len() + unsafe{&*root}.heap_len() + self.cells.len(),
            None => self.prog_cells.len() + self.cells.len(),
        }
        
    }

    fn get_id(&self) -> usize {
        self.id
    }
}

impl  Index<usize> for QueryHeap  {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.prog_cells.len() {
            &self.prog_cells[index]
        } else if self.root.is_none() {
            &self.cells[index - self.prog_cells.len()]
        } else{
            todo!("Handle Branching heap")
        }
    }
}

impl  IndexMut<usize> for QueryHeap  {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            panic!("Can't get mutable reference to program heap cell");
        } else if self.root.is_none(){
            &mut self.cells[index - self.prog_cells.len()]
        } else{
            todo!("Handle Branching heap")
        }
    }
}

impl  Index<Range<usize>> for QueryHeap {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.prog_cells.len();
        
        if index.start < len && index.end < len{
            &self.prog_cells[index]
        }else if index.start >= len && self.root.is_none(){
            &self.cells[index.start - len .. index.end - len]
        }else{
            panic!("Range splits static and mutable heap")
        }
    }
}