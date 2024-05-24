use crate::{symbol_db::SymbolDB, term::Term, unification};
use std::{
    collections::HashMap,
    mem,
    ops::{Deref, DerefMut, RangeInclusive},
    usize,
};
use unification::Binding;

use fsize::fsize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Tag {
    REF,
    REFC,
    REFA,
    STR,
    LIS,
    CON,
    INT,
    FLT,
    STR_REF,
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub type Cell = (Tag, usize);

pub struct Heap {
    pub(super) cells: Vec<Cell>,
    pub(super) symbols: SymbolDB,
    pub query_space: bool,
}

impl Heap {
    pub const REF: usize = usize::MAX;
    pub const REFC: usize = usize::MAX - 1;
    pub const REFA: usize = usize::MAX - 2;
    pub const STR: usize = usize::MAX - 3;
    pub const LIS: usize = usize::MAX - 4;
    pub const CON: usize = usize::MAX - 5;
    pub const INT: usize = usize::MAX - 6;
    pub const FLT: usize = usize::MAX - 7;
    pub const STR_REF: usize = usize::MAX - 8;
    pub const CON_PTR: usize = isize::MAX as usize;
    pub const FALSE: Cell = (Tag::CON, Heap::CON_PTR);
    pub const TRUE: Cell = (Tag::CON, Heap::CON_PTR + 1);
    pub const EMPTY_LIS: Cell = (Tag::LIS, Heap::CON_PTR);

    pub fn from_slice(cells: &[Cell]) -> Heap {
        let mut symbols = SymbolDB::new();
        symbols.set_const("false");
        symbols.set_const("true");
        Heap {
            cells: Vec::from(cells),
            query_space: true,
            symbols,
        }
    }

    pub fn new(size: usize) -> Heap {
        let mut symbols = SymbolDB::new();
        symbols.set_const("false");
        symbols.set_const("true");
        Heap {
            cells: Vec::with_capacity(size),
            query_space: true,
            symbols,
        }
    }

    pub fn set_var(&mut self, ref_addr: Option<usize>, universal: bool) -> usize {
        let addr = match ref_addr {
            Some(a) => a,
            None => self.cells.len(),
        };

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

    pub fn set_const(&mut self, id: usize) -> usize {
        self.cells.push((Tag::CON, id));
        return self.cells.len() - 1;
    }

    pub fn push(&mut self, cell: Cell) {
        self.cells.push(cell);
    }

    pub fn deref_addr(&self, addr: usize) -> usize {
        if let (Tag::REF | Tag::REFA | Tag::REFC | Tag::STR_REF, pointer) = self[addr] {
            if addr == pointer {
                addr
            } else {
                if self[addr].1 >= Heap::CON_PTR {
                    panic!("What: [{addr}] {:?}", self[addr])
                }
                self.deref_addr(self[addr].1)
            }
        } else {
            addr
        }
    }

    pub fn add_const_symbol(&mut self, symbol: &str) -> usize {
        self.symbols.set_const(symbol)
    }

    pub fn bind(&mut self, binding: &Binding) {
        for (src, target) in binding {
            if let (tag @ Tag::REF, pointer) = &mut self[*src] {
                if *pointer != *src {
                    self.print_heap();
                    panic!("Tried to reset bound ref: {} \n Binding: {binding:?}", src)
                }
                if *target >= Heap::CON_PTR {
                    *tag = Tag::CON;
                }
                *pointer = *target;
            }
        }
    }

    pub fn unbind(&mut self, binding: &Binding) {
        for (src, _target) in binding {
            if let (tag @ (Tag::REF | Tag::CON), pointer) = &mut self[*src] {
                if *tag == Tag::CON {
                    *tag = Tag::REF
                }
                *pointer = *src;
            }
        }
    }

    pub fn deallocate_str(&mut self, addr: usize) {
        let length = self[addr].1 + 2;
        if addr + length != self.cells.len() {
            self.print_heap();
            panic!("Deallocation error, addr:{addr}");
        }
        self.cells.truncate(self.cells.len() - length)
        //TO DO recursively delete structures pointed to within structure
    }

    pub fn deallocate_above(&mut self, addr: usize){
        self.cells.truncate(addr)
    }

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

    pub fn list_string(&self, addr: usize) -> String {
        let mut buffer = "[".to_string();
        let mut pointer = self[addr].1;
        // println!("{pointer}");
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
            Tag::STR_REF => self.structure_string(self[addr].1),
            _ => self.structure_string(addr),
        }
    }

    pub fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + 1 + self[addr].1
    }

    pub fn str_symbol_arity(&self, addr: usize) -> (usize, usize) {
        (self[addr + 1].1, self[addr].1)
    }

    pub fn create_var_symbols(&mut self, vars: Vec<usize>) {
        let mut alphabet = (b'A'..=b'Z').map(|c| String::from_utf8(vec![c]).unwrap());
        for var in vars {
            let symbol = alphabet.next().unwrap();
            self.symbols.set_var(&symbol, var)
        }
    }

    pub fn get_term_object(&self, addr: usize) -> Term {
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::STR => Term::STR(
                self.str_iterator(addr)
                    .map(|addr: usize| self.get_term_object(addr))
                    .collect(),
            ),
            Tag::STR_REF => Term::STR(
                self.str_iterator(self[addr].1)
                    .map(|addr: usize| self.get_term_object(addr))
                    .collect(),
            ),
            Tag::LIS => Term::LIS(todo!(), todo!()),
            Tag::REFC | Tag::REF => Term::VAR(match self.symbols.get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::REFA => Term::VARUQ(match self.symbols.get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::INT => Term::INT(unsafe { mem::transmute(self[addr].1) }),
            Tag::FLT => Term::FLT(unsafe { mem::transmute(self[addr].1) }),
            Tag::CON => Term::CON(self.symbols.get_const(self[addr].1).into()),
            _ => todo!(),
        }
    }

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

