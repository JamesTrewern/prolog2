use std::{ops::{Deref, DerefMut, Index, IndexMut, Range}, sync::{atomic::{AtomicUsize,Ordering::Acquire}, Arc, PoisonError, RwLock, RwLockReadGuard}};

use super::heap::{Cell, Heap, Tag, PROG_HEAP};

static HEAP_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);

pub struct QueryHeap<'a> {
    id: usize,
    arg_regs: [Cell; 64],
    pub(crate) cells: Vec<Cell>,
    prog_cells: Arc<Vec<Cell>>,
    //TODO handle branching query heap multi-threading
    root: Option<RwLockReadGuard<'a, QueryHeap<'a>>>,
}

impl<'a> QueryHeap<'a> {
    pub fn new(
        prog_cells: Arc<Vec<Cell>>,
        root: Option<RwLockReadGuard<'a, QueryHeap<'a>>>
    ) -> Result<QueryHeap<'a>, String> {
        let id = HEAP_ID_COUNTER.fetch_add(1, Acquire);
        Ok(QueryHeap {
            id,
            arg_regs: [(Tag::Ref, 0); 64],
            cells: Vec::new(),
            prog_cells,
            root,
        })
    }

    //Get cells as vector, allow root readguard to be dropped
    pub fn get_cells(self) -> Vec<Cell>{
        self.cells
    }
}

impl<'a> Heap for QueryHeap<'a> {
    fn heap_push(&mut self, cell: Cell) -> usize{
        let i = self.heap_len();
        self.cells.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        match &self.root {
            Some(root) => self.prog_cells.len() + root.heap_len() + self.cells.len(),
            None => self.prog_cells.len() + self.cells.len(),
        }
        
    }

    fn get_id(&self) -> usize {
        self.id
    }
}

impl<'a> Index<usize> for QueryHeap<'a> {
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

impl<'a> IndexMut<usize> for QueryHeap<'a> {
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

impl<'a> Index<Range<usize>> for QueryHeap<'a>{
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