use crate::binding::Binding;

use super::symbol_db::SymbolDB;
use std::ops::{Deref, DerefMut};

pub type Cell = (usize, usize);

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
    pub const CON_PTR: usize = isize::MAX as usize;

    pub fn new(size: usize) -> Heap {
        Heap {
            cells: Vec::with_capacity(size),
            query_space: true,
            symbols: SymbolDB::new(),
        }
    }

    pub fn set_var(&mut self, ref_addr: Option<usize>, universal: bool) -> usize {
        let addr = match ref_addr {
            Some(a) => a,
            None => self.cells.len(),
        };

        let tag = if universal {
            Heap::REFA
        } else if !self.query_space {
            Heap::REFC
        } else {
            Heap::REF
        };

        self.cells.push((tag, addr));
        return self.cells.len() - 1;
    }

    pub fn set_const(&mut self, id: usize) -> usize {
        self.cells.push((Heap::CON, id));
        return self.cells.len() - 1;
    }

    pub fn deref(&self, addr: usize) -> usize {
        if let (Heap::REF | Heap::REFA | Heap::REFC, pointer) = self[addr] {
            if addr == pointer {
                addr
            } else {
                self.deref(self[addr].1)
            }
        } else {
            addr
        }
    }

    pub fn deref_cell(&self, addr: usize) -> Option<Cell> {
        if addr < Heap::CON_PTR {
            Some(self[self.deref(addr)])
        } else {
            None
        }
    }

    pub fn add_const_symbol(&mut self, symbol: &str) -> usize {
        self.symbols.set_const(symbol)
    }

    pub fn duplicate(&mut self, start_i: usize, length: usize) -> usize {
        let new_start: usize = self.len();
        self.cells.extend_from_within(start_i..start_i + length);
        new_start
    }

    pub fn bind(&mut self, binding: &Binding) {
        for (src, target) in binding {
            if let (tag @ Heap::REF, pointer) = &mut self[*src] {
                if *pointer != *src {
                    self.print_heap();
                    panic!("Tried to reset bound ref: {} \n Binding: {binding:?}", src)
                }
                if *target >= Heap::CON_PTR {
                    *tag = Heap::CON;
                }
                // println!("{pointer} -> {target}");
                *pointer = *target;
            }
        }
    }

    pub fn unbind(&mut self, binding: &Binding) {
        for (src, _target) in binding {
            if let (tag @ (Heap::REF | Heap::CON), pointer) = &mut self[*src] {
                // print!(
                //     "[{src}],({}, {pointer}) -> ",
                //     match *tag {
                //         Heap::REF => "REF",
                //         Heap::CON => "CON",
                //         _ => "",
                //     }
                // );
                if *tag == Heap::CON {
                    *tag = Heap::REF
                }
                *pointer = *src;
                // println!(
                //     "({}, {pointer})",
                //     match *tag {
                //         Heap::REF => "REF",
                //         Heap::CON => "CON",
                //         _ => "",
                //     }
                // );
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

    pub fn print_heap(&self) {
        let w = 6;
        for (i, cell) in self.iter().enumerate() {
            match cell.0 {
                Heap::CON => {
                    println!(
                        "[{:3}]|{:w$}|{:w$}|",
                        i,
                        "CON",
                        self.symbols.get_const(cell.1)
                    )
                }
                Heap::STR => {
                    println!("[{:3}]|{:w$}|{:w$}|", i, "STR", cell.1)
                }
                Heap::LIS => {
                    if cell.1 == Heap::CON {
                        println!("[{:3}]|{:w$}|{:w$}|", i, "LIS", "[]")
                    } else {
                        println!("[{:3}]|{:w$}|{:w$}|", i, "LIS", cell.1)
                    }
                }
                Heap::REF | Heap::REFA | Heap::REFC => {
                    println!(
                        "[{:3}]|{:w$?}|{:w$}|:({})",
                        i,
                        match cell.0 {
                            Heap::REF => "REF",
                            Heap::REFA => "REFA",
                            Heap::REFC => "REFC",
                            _ => "",
                        },
                        cell.1,
                        self.symbols.get_symbol(self.deref(i))
                    )
                }
                id => {
                    println!(
                        "[{:3}]|{:>w$}/{:<w$}|",
                        i,
                        self.symbols.get_symbol(id),
                        cell.1
                    )
                }
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
            if self[pointer + 1].0 != Heap::LIS {
                buffer += "|";
                buffer += &self.term_string(pointer + 1);
                break;
            } else {
                buffer += ",";
            }
            pointer = self[pointer + 1].1;
            if pointer == Heap::CON {
                buffer.pop();
                break;
            }
        }
        buffer += "]";
        buffer
    }

    pub fn structure_string(&self, addr: usize) -> String {
        let (_, arity) = self[addr];
        let mut buf = self.term_string(addr + 1);
        buf += "(";
        for i in 1..=arity {
            buf += &self.term_string(addr + 1 + i);
            buf += ","
        }
        buf.pop();
        buf += ")";
        buf
    }

    pub fn term_string(&self, addr: usize) -> String {
        let addr = self.deref(addr);
        match self[addr].0 {
            Heap::CON => self.symbols.get_const(self[addr].1).to_owned(),
            Heap::STR => self.structure_string(addr),
            Heap::LIS => self.list_string(addr),
            Heap::REF | Heap::REFC => match self.symbols.get_var(self.deref(addr)).to_owned() {
                Some(symbol) => symbol.to_owned(),
                None => format!("_{addr}"),
            },
            Heap::REFA => {
                if let Some(symbol) = self.symbols.get_var(self.deref(addr)) {
                    format!("∀'{symbol}")
                } else {
                    format!("∀'_{addr}")
                }
            }
            _ => self.structure_string(addr),
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