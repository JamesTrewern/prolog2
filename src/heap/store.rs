use crate::interface::state::State;
use super::symbol_db::SymbolDB;
use fsize::fsize;
use manual_rwlock::SliceReadGaurd;
use std::{
    fmt::Debug,
    mem,
    ops::{Index, IndexMut, RangeInclusive},
};

const HEAP_SIZE: usize = 2000;
const ARG_REGS: usize = 64;
/** Tag which describes cell type */
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    pub fn len(&self) -> usize {
        self.prog_cells.len() + self.cells.len()
    }

    /**Recursively dereference cell address until non ref or self ref cell */
    pub fn deref_addr(&self, mut addr: usize) -> usize {
        loop {
            if let (Tag::Ref | Tag::Str, pointer) = self[addr] {
                if addr == pointer {
                    return pointer;
                } else {
                    addr = pointer
                }
            } else {
                return addr;
            }
        }
    }

    pub fn set_const(&mut self, id: usize) -> usize {
        let h = self.len();
        self.cells.push((Tag::Con, id));
        h
    }

    /**Create new variable on heap
     * @ref_addr: optional value, if None create self reference
     * @universal: is the new var universally quantified
     */
    pub fn set_ref(&mut self, ref_addr: Option<usize>) -> usize {
        //If no address provided set addr to current heap len
        let addr = match ref_addr {
            Some(a) => a,
            None => self.len(),
        };
        self.cells.push((Tag::Ref, addr));
        return self.len() - 1;
    }

    /**Create new variable on heap
     * @ref_addr: optional value, if None create self reference
     * @universal: is the new var universally quantified
     */
    pub fn set_arg(&mut self, value: usize, ho: bool) -> usize {
        //If no address provided set addr to current heap len
        self.cells
            .push((if ho { Tag::ArgA } else { Tag::Arg }, value));
        return self.cells.len() - 1;
    }

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    pub fn bind(&mut self, binding: &[(usize, usize)]) {
        for (src, target) in binding {
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

    /**Debug function for printing formatted string of current heap state */
    pub fn print_heap(&self) {
        let w = 6;
        for i in 0..self.len() {
            let (tag, value) = self[i];
            match tag {
                Tag::Con => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", SymbolDB::get_const(value))
                }
                Tag::Lis => {
                    if value == Self::CON_PTR {
                        println!("[{i:3}]|{tag:w$}|{:w$}|", "[]")
                    } else {
                        println!("[{i:3}]|{tag:w$}|{value:w$}|")
                    }
                }
                Tag::Ref | Tag::ArgA | Tag::Arg => {
                    println!(
                        "[{i:3}]|{tag:w$?}|{value:w$}|:({})",
                        SymbolDB::get_symbol(self.deref_addr(i))
                    )
                }
                Tag::Int => {
                    let value: isize = unsafe { mem::transmute_copy(&value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                Tag::Flt => {
                    let value: fsize = unsafe { mem::transmute_copy(&value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                _ => println!("[{i:3}]|{tag:w$?}|{value:w$}|"),
            };
            println!("{:-<w$}--------{:-<w$}", "", "");
        }
    }

    /**Create a string from a list */
    pub fn list_string(&self, addr: usize) -> String {
        if self[addr] == Self::EMPTY_LIS {
            return "[]".to_string();
        }

        let mut buffer = "[".to_string();
        let mut pointer = self[addr].1;

        loop {
            buffer += &self.term_string(pointer);
            if self[pointer + 1].0 != Tag::Lis {
                buffer += "|";
                buffer += &self.term_string(pointer + 1);
                break;
            } else {
                buffer += ",";
            }
            pointer = self[pointer + 1].1;
            if pointer == Self::CON_PTR {
                buffer.pop();
                break;
            }
        }
        buffer += "]";
        buffer
    }

    /**Create a string for a structure */
    pub fn structure_string(&self, addr: usize) -> String {
        let mut buf = "".to_string();
        let mut first = true;
        for i in self.str_iterator(addr) {
            buf += &self.term_string(i);
            buf += if first { "(" } else { "," };
            if first {
                first = false
            }
        }
        buf.pop();
        buf += ")";
        buf
    }

    /** Create String to represent cell, can be recursively used to format complex structures or list */
    pub fn term_string(&self, addr: usize) -> String {
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Con => SymbolDB::get_const(self[addr].1).to_string(),
            Tag::Func => self.structure_string(addr),
            Tag::Lis => self.list_string(addr),
            Tag::Ref | Tag::Arg => match SymbolDB::get_var(self.deref_addr(addr)).to_owned() {
                Some(symbol) => symbol.to_string(),
                None => format!("_{addr}"),
            },
            Tag::ArgA => {
                if let Some(symbol) = SymbolDB::get_var(self.deref_addr(addr)) {
                    format!("∀'{symbol}")
                } else {
                    format!("∀'_{addr}")
                }
            }
            Tag::Int => {
                let value: isize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Flt => {
                let value: fsize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Str => self.structure_string(self[addr].1),
        }
    }

    /** Given address to a str cell create an operator over the sub terms addresses, including functor/predicate */
    pub fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + self[addr].1
    }

    /** Given address to str cell return tuple for (symbol, arity)
     * If symbol is greater than isize::MAX then it is a constant id
     * If symbol is lower that isize::Max then it is a reference address
     */
    pub fn str_symbol_arity(&self, addr: usize) -> (usize, usize) {
        let symbol = self[self.deref_addr(addr + 1)].1;
        (symbol, self[addr].1)
    }

    pub fn push(&mut self, cell: Cell) {
        self.cells.push(cell);
    }

    /**Collect all REF, REFC, and REFA cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    pub fn term_vars(&self, mut addr: usize) -> Vec<Cell> {
        addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Ref | Tag::Arg | Tag::ArgA => vec![self[addr]],
            Tag::Lis if self[addr].1 != Self::CON_PTR => [
                self.term_vars(self[addr].1),
                self.term_vars(self[addr].1 + 1),
            ]
            .concat(),
            Tag::Func => self
                .str_iterator(addr)
                .map(|addr| self.term_vars(addr))
                .collect::<Vec<Vec<Cell>>>()
                .concat(),
            _ => vec![],
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
