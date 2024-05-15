use crate::{symbol_db::SymbolDB, unification};
use std::{
    collections::HashMap,
    ops::{Deref, DerefMut, RangeInclusive},
};
use unification::Binding;

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
    pub const STR_REF: usize = usize::MAX - 8;
    pub const CON_PTR: usize = isize::MAX as usize;
    pub const EMPTY_LIS: Cell = (Heap::LIS, Heap::CON);

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

    pub fn push(&mut self, cell: Cell) {
        self.cells.push(cell);
    }

    pub fn deref_addr(&self, addr: usize) -> usize {
        if let (Heap::REF | Heap::REFA | Heap::REFC | Heap::STR_REF, pointer) = self[addr] {
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
            if let (tag @ Heap::REF, pointer) = &mut self[*src] {
                if *pointer != *src {
                    self.print_heap();
                    panic!("Tried to reset bound ref: {} \n Binding: {binding:?}", src)
                }
                if *target >= Heap::CON_PTR {
                    *tag = Heap::CON;
                }
                *pointer = *target;
            }
        }
    }

    pub fn unbind(&mut self, binding: &Binding) {
        for (src, _target) in binding {
            if let (tag @ (Heap::REF | Heap::CON), pointer) = &mut self[*src] {
                if *tag == Heap::CON {
                    *tag = Heap::REF
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
                Heap::STR_REF => {
                    println!("[{:3}]|{:w$}|{:w$}|", i, "STREF", cell.1)
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
                        self.symbols.get_symbol(self.deref_addr(i))
                    )
                }
                Heap::INT => {
                    println!(
                        "[{:3}]|{:w$?}|{:w$}|",
                        i,
                        "INT",
                        cell.1
                    )
                }
                _ => panic!("Unkown Tag"),
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
        let mut buf = "".to_string();
        let mut first = true;
        for i in self.str_iterator(addr){
            buf += &self.term_string(i);
            buf += if first {"("} else {","};
            if first { first = false}
        }
        buf.pop();
        buf += ")";
        buf
    }

    pub fn term_string(&self, addr: usize) -> String {
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Heap::CON => self.symbols.get_const(self[addr].1).to_owned(),
            Heap::STR => self.structure_string(addr),
            Heap::LIS => self.list_string(addr),
            Heap::REF | Heap::REFC => {
                match self.symbols.get_var(self.deref_addr(addr)).to_owned() {
                    Some(symbol) => symbol.to_owned(),
                    None => format!("_{addr}"),
                }
            }
            Heap::REFA => {
                if let Some(symbol) = self.symbols.get_var(self.deref_addr(addr)) {
                    format!("∀'{symbol}")
                } else {
                    format!("∀'_{addr}")
                }
            }
            Heap::INT => {
                format!("{}", self[addr].1)
            }
            Heap::STR_REF => self.structure_string(self[addr].1),
            _ => self.structure_string(addr),
        }
    }

    pub fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + 1 + self[addr].1
    }

    pub fn str_symbol_arity(&self, addr: usize) -> (usize, usize) {
        (self[addr + 1].1, self[addr].1)
    }
}

#[derive(Clone)]
enum SubTerm {
    TEXT(String),
    CELL((usize, usize)),
}

impl Heap {
    fn text_var(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        match symbols_map.get(text) {
            Some(ref_addr) => self.set_var(Some(*ref_addr), uni_vars.contains(&text)),
            None => {
                let addr = self.set_var(None, uni_vars.contains(&text));
                symbols_map.insert(text.to_owned(), addr);
                self.symbols.set_var(text, addr);
                addr
            }
        }
    }
    fn text_const(&mut self, text: &str, symbols_map: &mut HashMap<String, usize>) -> usize {
        let id = self.symbols.set_const(text);
        self.set_const(id)
    }
    fn text_number(&mut self, text: &str) -> usize {
        if text.contains('.') {
            todo!("parse floats")
        } else {
            match text.parse::<usize>() {
                Ok(value) => {
                    self.push((Heap::INT, value));
                    self.len() - 1
                }
                Err(_) => panic!("Cannot parse number"),
            }
        }
    }
    fn text_singlet(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        if text.chars().next().unwrap().is_ascii_digit() {
            self.text_number(text)
        } else if text.chars().next().unwrap().is_uppercase() {
            self.text_var(text, symbols_map, uni_vars)
        } else {
            self.text_const(text, symbols_map)
        }
    }

    fn handle_sub_terms(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> Vec<SubTerm> {
        let mut last_i: usize = 0;
        let mut in_brackets = (0, 0);
        let mut subterms_txt: Vec<&str> = vec![];
        for (i, c) in text.chars().enumerate() {
            match c {
                '(' => {
                    in_brackets.0 += 1;
                }
                ')' => {
                    if in_brackets.0 == 0 {
                        break;
                    }
                    in_brackets.0 -= 1;
                }
                '[' => {
                    in_brackets.1 += 1;
                }
                ']' => {
                    if in_brackets.1 == 0 {
                        break;
                    }
                    in_brackets.1 -= 1;
                }
                ',' => {
                    if in_brackets == (0, 0) {
                        subterms_txt.push(&text[last_i..i]);
                        last_i = i + 1
                    }
                }
                _ => (),
            }
        }
        subterms_txt.push(&text[last_i..]);
        subterms_txt
            .iter()
            .map(|sub_term| {
                if complex_term(sub_term) {
                    self.build_heap_term_rec(sub_term, symbols_map, uni_vars)
                } else {
                    SubTerm::TEXT(sub_term.to_string())
                }
            })
            .collect()
    }

    fn text_structure(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        let i1 = text.find('(').unwrap();
        let i2 = text.rfind(')').unwrap();
        let sub_terms = self.handle_sub_terms(&text[i1 + 1..i2], symbols_map, uni_vars);
        let i = self.cells.len();
        self.cells.push((Heap::STR, sub_terms.len()));
        self.text_singlet(&text[..i1], symbols_map, uni_vars);
        for sub_term in sub_terms {
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => self.cells.push(cell),
            }
        }
        SubTerm::CELL((Heap::STR_REF, i))
    }

    fn text_list(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        if text == "[]" {
            return SubTerm::CELL(Heap::EMPTY_LIS);
        }
        let i1 = text.find('[').unwrap() + 1;
        let mut i2 = text.rfind(']').unwrap();
        let mut explicit_tail = false;
        i2 = match text.rfind('|') {
            Some(i) => {
                explicit_tail = true;
                i
            }
            None => i2,
        };
        let subterms = self.handle_sub_terms(&text[i1..i2], symbols_map, uni_vars);
        let tail = if explicit_tail {
            Some(
                self.handle_sub_terms(
                    &text[i2 + 1..text.rfind(']').unwrap()],
                    symbols_map,
                    uni_vars,
                )[0]
                .clone(),
            )
        } else {
            None
        };
        let i = self.cells.len();
        for sub_term in subterms {
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.cells.push(cell);
                }
            }
            self.cells.push((Heap::LIS, self.cells.len() + 1))
        }
        self.cells.pop(); //Remove last LIS tag cell
        match tail {
            Some(sub_term) => match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.cells.push(cell);
                }
            },
            None => self.cells.push(Heap::EMPTY_LIS),
        }
        SubTerm::CELL((Heap::LIS, i))
    }

    fn build_heap_term_rec(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        let list_open = match text.find('[') {
            Some(i) => i,
            None => usize::MAX,
        };
        let brackets_open = match text.find('(') {
            Some(i) => i,
            None => usize::MAX,
        };
        if list_open == usize::MAX && brackets_open == usize::MAX {
            panic!("help")
        } else {
            if list_open < brackets_open {
                self.text_list(text, symbols_map, uni_vars)
            } else {
                self.text_structure(text, symbols_map, uni_vars)
            }
        }
    }

    pub fn build_literal(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        match self.build_heap_term_rec(text, symbols_map, uni_vars) {
            SubTerm::TEXT(_) => self.cells.len() - 1,
            SubTerm::CELL((Heap::STR, i)) => i,
            SubTerm::CELL((Heap::LIS, i)) => {
                self.cells.push((Heap::LIS, i));
                self.cells.len() - 1
            }
            SubTerm::CELL((Heap::REF | Heap::STR_REF, i)) => self.deref_addr(i),
            SubTerm::CELL((tag, i)) => panic!("Unkown LIteral type: ({tag},{i}"),
        }
    }
}

fn complex_term(text: &str) -> bool {
    text.chars().any(|c| c == '(' || c == '[')
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
