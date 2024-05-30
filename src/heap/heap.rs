use super::symbol_db::SymbolDB;
use std::{
    mem,
    ops::{Deref, DerefMut, RangeInclusive},
    usize,
};
use fsize::fsize;

/** Tag which describes cell type */
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum Tag {
    REF,    //Query Variable
    REFC,   //Clause Variable
    REFA,   //Universally Quantified variable
    STR,    //Structure
    LIS,    //List
    CON,    //Constant
    INT,    //Integer
    FLT,    //Float
    StrRef, //Reference to Structure
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub type Cell = (Tag, usize);

/** Heap data structure
 * Stores contigious block of cells describing all compliled terms
 */
pub(crate) struct Heap {
    cells: Vec<Cell>,
    pub symbols: SymbolDB,
    pub query_space: bool,
    pub query_space_pointer: usize,
}

impl Heap {
    pub const CON_PTR: usize = isize::MAX as usize;
    pub const FALSE: Cell = (Tag::CON, Heap::CON_PTR);
    pub const TRUE: Cell = (Tag::CON, Heap::CON_PTR + 1);
    pub const EMPTY_LIS: Cell = (Tag::LIS, Heap::CON_PTR);

    /** Builds a new heap from a reference to a slice of cells, used for creating test instances */
    pub fn from_slice(cells: &[Cell]) -> Heap {
        Heap {
            cells: Vec::from(cells),
            query_space: true,
            query_space_pointer: 0,
            symbols: SymbolDB::new(),
        }
    }

    pub fn new(size: usize) -> Heap {
        Heap {
            cells: Vec::with_capacity(size),
            query_space_pointer: 0,
            query_space: true,
            symbols: SymbolDB::new(),
        }
    }

    /**Create new variable on heap
     * @ref_addr: optional value, if None create self reference
     * @universal: is the new var universally quantified
     */
    pub fn set_var(&mut self, ref_addr: Option<usize>, universal: bool) -> usize {
        //If no address provided set addr to current heap len
        let addr = match ref_addr {
            Some(a) => a,
            None => self.cells.len(),
        };

        //Define variable cell tag
        let tag = if universal {
            Tag::REFA
        } else if !self.query_space {
            Tag::REFC
        } else {
            Tag::REF
        };

        self.cells.push((tag, addr));
        return self.cells.len() - 1;
    }

    /**Create new constant on heap
     * @id: integer which represents constant symbol (held by symbol db)
     */
    pub fn set_const(&mut self, id: usize) -> usize {
        self.cells.push((Tag::CON, id));
        return self.cells.len() - 1;
    }

    /**Push cell to heap */
    pub fn push(&mut self, cell: Cell) {
        self.cells.push(cell);
    }

    /**Recursively dereference cell address until non ref or self ref cell */
    pub fn deref_addr(&self, addr: usize) -> usize {
        if let (Tag::REF | Tag::REFA | Tag::REFC | Tag::StrRef, pointer) = self[addr] {
            if addr == pointer {
                addr
            } else {
                self.deref_addr(self[addr].1)
            }
        } else {
            addr
        }
    }

    /**Add new constant symbol to symbol database and return ID*/
    pub fn add_const_symbol(&mut self, symbol: &str) -> usize {
        self.symbols.set_const(symbol)
    }

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    */
    pub fn bind(&mut self, binding: &[(usize,usize)]) {
        for (src, target) in binding {
            if let (Tag::REF, pointer) = &mut self[*src] {
                if *pointer != *src {
                    self.print_heap();
                    panic!("Tried to reset bound ref: {} \n Binding: {binding:?}", src)
                }
                *pointer = *target;
            }
        }
    }

    /** Reset Ref cells affected by binding to self references
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    */
    pub fn unbind(&mut self, binding: &[(usize,usize)]) {
        for (src, _target) in binding {
            if let (tag @ (Tag::REF | Tag::CON), pointer) = &mut self[*src] {
                if *tag == Tag::CON {
                    *tag = Tag::REF
                }
                *pointer = *src;
            }
        }
    }

    /**Dealocate all heap cells above a certain address */
    pub fn deallocate_above(&mut self, addr: usize){
        if addr > self.query_space_pointer{
            self.cells.truncate(addr)
            //Effect symbol db to remove vars above this point
        }
    }

    /**Debug function for printing formatted string of current heap state */
    pub fn print_heap(&self) {
        let w = 6;
        for (i, (tag, value)) in self.iter().enumerate() {
            match tag {
                Tag::CON => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", self.symbols.get_const(*value))
                }
                Tag::LIS => {
                    if *value == Heap::CON_PTR {
                        println!("[{i:3}]|{tag:w$}|{:w$}|", "[]")
                    } else {
                        println!("[{i:3}]|{tag:w$}|{value:w$}|")
                    }
                }
                Tag::REF | Tag::REFA | Tag::REFC => {
                    println!(
                        "[{i:3}]|{tag:w$?}|{value:w$}|:({})",
                        self.symbols.get_symbol(self.deref_addr(i))
                    )
                }
                Tag::INT => {
                    let value: isize = unsafe { mem::transmute_copy(value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                Tag::FLT => {
                    let value: fsize = unsafe { mem::transmute_copy(value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                _ => println!("[{i:3}]|{tag:w$?}|{value:w$}|"),
            };
            println!("{:-<w$}--------{:-<w$}", "", "");
        }
    }

    /**Create a string from a list */
    pub fn list_string(&self, addr: usize) -> String {
        let mut buffer = "[".to_string();
        let mut pointer = self[addr].1;
        loop {
            buffer += &self.term_string(pointer);
            if self[pointer + 1].0 != Tag::LIS {
                buffer += "|";
                buffer += &self.term_string(pointer + 1);
                break;
            } else {
                buffer += ",";
            }
            pointer = self[pointer + 1].1;
            if pointer == Heap::CON_PTR {
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
            Tag::CON => self.symbols.get_const(self[addr].1).to_owned(),
            Tag::STR => self.structure_string(addr),
            Tag::LIS => self.list_string(addr),
            Tag::REF | Tag::REFC => match self.symbols.get_var(self.deref_addr(addr)).to_owned() {
                Some(symbol) => symbol.to_owned(),
                None => format!("_{addr}"),
            },
            Tag::REFA => {
                if let Some(symbol) = self.symbols.get_var(self.deref_addr(addr)) {
                    format!("∀'{symbol}")
                } else {
                    format!("∀'_{addr}")
                }
            }
            Tag::INT => {
                let value: isize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::FLT => {
                let value: fsize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::StrRef => self.structure_string(self[addr].1),
        }
    }

    /** Given address to a str cell create an operator over the sub terms addresses, including functor/predicate */
    pub fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + 1 + self[addr].1
    }

    /** Given address to str cell return tuple for (symbol, arity)
     * If symbol is greater than isize::MAX then it is a constant id
     * If symbol is lower that isize::Max then it is a reference address
    */
    pub fn str_symbol_arity(&self, addr: usize) -> (usize, usize) {
        let symbol = self[self.deref_addr(addr + 1)].1;
        (symbol, self[addr].1)
    }

    /**Collect all REF, REFC, and REFA cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    pub fn term_vars(&self, mut addr: usize) -> Vec<Cell>{
        addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::REF | Tag::REFA | Tag::REFC => vec![self[addr]],
            Tag::LIS if self[addr].1 != Heap::CON_PTR => [self.term_vars(self[addr].1), self.term_vars(self[addr].1+1)].concat(),
            Tag::STR => self.str_iterator(addr).map(|addr| self.term_vars(addr)).collect::<Vec<Vec<Cell>>>().concat(),
            _ => vec![],
        }
    }
}

impl Deref for Heap {
    type Target = [Cell];
    fn deref(&self) -> &[Cell] {
        &self.cells
    }
}

impl DerefMut for Heap {
    fn deref_mut(&mut self) -> &mut [Cell] {
        &mut self.cells
    }
}

