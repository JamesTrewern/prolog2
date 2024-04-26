use crate::binding::Binding;

use super::symbol_db::SymbolDB;
use std::{
    alloc::{alloc, Layout},
    collections::HashMap,
    ops::{Deref, DerefMut},
    ptr,
};

pub type Cell = (usize, usize);

pub struct HeapDeallocationError;

pub struct Heap {
    ptr: *mut Cell,
    cap: usize,
    len: usize,
    pub query_space: bool,
    pub symbols: SymbolDB,
}
#[derive(Debug, Clone)]
enum SubTerm {
    TEXT(String),
    CELL((usize, usize)),
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
        let layout = Layout::array::<Cell>(size).unwrap();
        assert!(layout.size() <= isize::MAX as usize, "Allocation too large");
        let ptr = unsafe { alloc(layout) } as *mut Cell;
        Heap {
            ptr,
            cap: size,
            len: 0,
            query_space: true,
            symbols: SymbolDB::new(),
        }
    }

    pub fn set_var(&mut self, ref_addr: Option<usize>, universal: bool) -> usize {
        if self.len == self.cap {
            panic!("Heap out of memory")
        }
        let addr = match ref_addr {
            Some(a) => a,
            None => self.len,
        };
        unsafe {
            ptr::write(
                self.ptr.add(self.len),
                (
                    if universal {
                        Heap::REFA
                    } else if !self.query_space {
                        Heap::REFC
                    } else {
                        Heap::REF
                    },
                    addr,
                ),
            );
        }
        self.len += 1;
        return self.len - 1;
    }

    pub fn set_const(&mut self, id: usize) -> usize {
        if self.len == self.cap {
            panic!("Heap out of memory")
        }
        unsafe {
            ptr::write(self.ptr.add(self.len), (Heap::CON, id));
        }
        self.len += 1;
        return self.len - 1;
    }

    pub fn put_structure(&mut self, symbol: usize, arity: usize) -> usize {
        unsafe {
            ptr::write(self.ptr.add(self.len), (symbol, arity));
        }
        self.len += 1;
        self.len - 1
    }

    pub fn put_list(&mut self, empty: bool) {
        let pointer = if empty { Heap::CON } else { self.len + 1 };
        unsafe {
            ptr::write(self.ptr.add(self.len), (Heap::LIS, pointer));
        }
        self.len += 1;
    }

    pub fn put_cell(&mut self, cell: (usize, usize)) {
        unsafe {
            ptr::write(self.ptr.add(self.len), cell);
        }
        self.len += 1;
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

    pub fn deref_str_head(&self, addr: usize) -> Cell{
        let (mut symbol, arity) = self[addr];

        if symbol < Heap::CON_PTR{
            symbol = self[self.deref(symbol)].1;
        }

        (symbol,arity)
    }

    pub fn deref_cell(&self, addr: usize) -> Option<Cell> {
        if addr < Heap::CON_PTR {
            Some(self[self.deref(addr)])
        }else{
            None
        }
    }

    pub fn add_const_symbol(&mut self, symbol: &str) -> usize {
        self.symbols.set_const(symbol)
    }

    pub fn duplicate(&mut self, start_i: usize, length: usize) -> usize {
        let new_start: usize = self.len();
        unsafe {
            let src = self.ptr.add(start_i);
            let dst = self.ptr.add(self.len);
            ptr::copy(src, dst, length);
            self.len += length;
        }
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

    pub fn deallocate_str(&mut self, addr: usize){
        let cell = self.deref_str_head(addr);

        if addr + cell.1 + 1 != self.len{
            self.print_heap();
            panic!("Deallocation error, addr:{addr}");
        }

        println!("{},{addr}",cell.0);
        if cell.0 < Heap::CON_PTR && cell.0 + 1 == addr{
            self.len -= cell.1 + 2;
        }else{
            self.len -= cell.1 + 1;
        }
        //TO DO recursively delete structures pointed to within structure
    }

    //-----------------------------------------------------------------------------------------------

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
    fn text_singlet(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        if text.chars().next().unwrap().is_uppercase() {
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

    fn text_compound(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        let i1 = text.find('(').unwrap();
        let i2 = text.rfind(')').unwrap();
        let sub_terms = self.handle_sub_terms(&text[i1 + 1..i2], symbols_map, uni_vars);
        //If var head pass to text var
        let symbol = if text.chars().next().unwrap().is_uppercase() {
            self.text_var(&text[..i1], symbols_map, uni_vars)
        } else {
            self.symbols.set_const(&text[..i1])
        };
        let i = self.put_structure(symbol, sub_terms.len());
        for sub_term in sub_terms {
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => self.put_cell(cell),
            }
        }
        SubTerm::CELL((Heap::STR, i))
    }

    fn text_list(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
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
        let i = self.len + 1;
        for sub_term in subterms {
            self.put_list(false);
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.put_cell(cell);
                }
            }
        }
        match tail {
            Some(sub_term) => match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.put_cell(cell);
                }
            },
            None => self.put_list(true),
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
                self.text_compound(text, symbols_map, uni_vars)
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
            SubTerm::TEXT(_) => self.len - 1,
            SubTerm::CELL((_str, i)) => i,
        }
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

        let mut symbol_id = self[addr].0;
        if symbol_id < Heap::CON_PTR{
            symbol_id = self[self.deref(symbol_id)].1
        }

        let mut buf = self.symbols.get_symbol(symbol_id);
        buf += "(";
        for i in addr + 1..addr + self[addr].1 + 1 {
            buf += &self.term_string(i);
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
            Heap::STR => self.structure_string(self[addr].1),
            Heap::LIS => self.list_string(addr),
            Heap::REF | Heap::REFC => match self.symbols.get_var(addr).to_owned() {
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
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl DerefMut for Heap {
    fn deref_mut(&mut self) -> &mut [Cell] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

fn complex_term(text: &str) -> bool {
    text.chars().any(|c| c == '(' || c == '[')
}
