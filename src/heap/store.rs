use super::heap::Heap;
use manual_rwlock::SliceReadGaurd;
use std::{ fmt::Debug, ops::{Index, IndexMut, Range}
};

const HEAP_SIZE: usize = 2000;
const ARG_REGS: usize = 64;
/** Tag which describes cell type */
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum Tag {
    Ref,  //Query Variable
    Arg,  //Clause Variable
    ArgA, //Universally Quantified variable
    Func, //Structure
    Lis,  //List
    Con,  //Constant
    Int,  //Integer
    Flt,  //Float
    Str,  //Reference to Structure
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub type Cell = (Tag, usize);

#[derive(Clone)]
pub(crate) struct Store<'a> {
    pub arg_regs: [usize; ARG_REGS],
    pub prog_cells: SliceReadGaurd<'a, Cell>,
    pub cells: Vec<Cell>,
}

impl<'a> Heap for Store<'a> {
    fn heap_push(&mut self, cell: Cell) {
        self.cells.push(cell)
    }

    fn heap_len(&self) -> usize {
        self.prog_cells.len() + self.cells.len()
    }
}

impl<'a> Store<'a> {
    pub const CON_PTR: usize = isize::MAX as usize;
    pub const FALSE: Cell = (Tag::Con, Self::CON_PTR);
    pub const TRUE: Cell = (Tag::Con, Self::CON_PTR + 1);
    pub const EMPTY_LIS: Cell = (Tag::Lis, Self::CON_PTR);

    pub fn new(prog_cells: SliceReadGaurd<'a, Cell>) -> Store {
        Store {
            arg_regs: [usize::MAX; 64],
            cells: Vec::with_capacity(HEAP_SIZE),
            prog_cells,
        }
    }
    pub fn reset_args(&mut self) {
        self.arg_regs = [usize::MAX; ARG_REGS];
    }

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    pub fn bind(&mut self, binding: &[(usize, usize)]) {
        for (src, target) in binding {
            println!("{}", self.term_string(*src));
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

impl<'a> Index<usize> for Store<'a> {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.prog_cells.len() {
            &self.prog_cells[index]
        } else {
            &self.cells[index - self.prog_cells.len()]
        }
    }
}

impl<'a> IndexMut<usize> for Store<'a> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            panic!("Can't get mutable reference to program heap cell");
        } else {
            &mut self.cells[index - self.prog_cells.len()]
        }
    }
}

impl<'a> Index<Range<usize>> for Store<'a>{
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.prog_cells.len();
        if index.start < len && index.end < len{
            &self.prog_cells[index]
        }else if index.start >= len {
            &self.cells[index.start - len .. index.end - len]
        }else{
            panic!("Range splits static and mutable heap")
        }
    }
}

pub(crate) struct ListIter<'a> {
    pub store: &'a Store<'a>,
    pub index: usize 
}

impl<'a> Iterator for ListIter<'a> {
    type Item = (Cell, bool);

    fn next(&mut self) -> Option<Self::Item> {
        if let (Tag::Lis, pointer) = self.store[self.index]{
            if pointer == Store::CON_PTR{
                None
            }else{
                self.index = pointer + 1;
                Some((self.store[pointer], false))
            }
        }else{
            Some((self.store[self.index], true))
        }
    }
}