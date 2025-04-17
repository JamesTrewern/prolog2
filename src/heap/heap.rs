use std::{
    mem,
    ops::{Index, IndexMut, Range, RangeInclusive}, sync::RwLock,
};

use super::symbol_db::SymbolDB;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum Tag {
    Ref,  //Query Variable
    Arg,  //Clause Variable
    Func, //Functor + tuple
    Tup,  //Tuple
    Set,  //Set
    Lis,  //List
    Con,  //Constant
    Int,  //Integer
    Flt,  //Float
    Str,  //Reference to Structure
    Stri, //String
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub type Cell = (Tag, usize);

use fsize::fsize;
pub const CON_PTR: usize = isize::MAX as usize;
pub const FALSE: Cell = (Tag::Con, CON_PTR);
pub const TRUE: Cell = (Tag::Con, CON_PTR + 1);
pub const EMPTY_LIS: Cell = (Tag::Lis, CON_PTR);

pub trait Heap: IndexMut<usize, Output = Cell> + Index<Range<usize>, Output = [Cell]> {
    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn get_id(&self) -> usize{
        0
    }

    fn set_arg(&mut self, value: usize) -> usize {
        //If no address provided set addr to current heap len
        self.heap_push((Tag::Arg, value));
        return self.heap_len() - 1;
    }

    fn set_const(&mut self, id: usize) -> usize {
        let h = self.heap_len();
        self.heap_push((Tag::Con, id));
        h
    }

    fn set_ref(&mut self, ref_addr: Option<usize>) -> usize {
        //If no address provided set addr to current heap len
        let addr = match ref_addr {
            Some(a) => a,
            None => self.heap_len(),
        };
        self.heap_push((Tag::Ref, addr));
        return self.heap_len() - 1;
    }

    fn deref_addr(&self, mut addr: usize) -> usize {
        loop {
            if let (Tag::Ref, pointer) = self[addr] {
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

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    fn bind(&mut self, binding: &[(usize, usize)]) {
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
    fn unbind(&mut self, binding: &[(usize, usize)]) {
        for (src, _target) in binding {
            if let (Tag::Ref, pointer) = &mut self[*src] {
                *pointer = *src;
            }
        }
    }

    /**Get the symbol id and arity of functor structure */
    fn str_symbol_arity(&self, mut addr: usize) -> (usize, usize) {
        addr = self.deref_addr(addr);
        if let (Tag::Str, pointer) = self[addr] {
            addr = pointer
        }
        if let (Tag::Func, arity) = self[addr] {
            (self[self.deref_addr(addr + 1)].1, arity)
        } else if let (Tag::Con, symbol) = self[addr] {
            (symbol, 0)
        } else {
            panic!(
                "No str arity for {}, {:?}",
                self.term_string(addr),
                self[addr]
            )
        }
    }

    /**Collect all REF, cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    fn term_vars(&self, mut addr: usize) -> Vec<Cell> {
        addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Ref | Tag::Arg => vec![self[addr]],
            Tag::Lis if self[addr].1 != CON_PTR => [
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

    /** Given address to a str cell create an operator over the sub terms addresses, including functor/predicate */
    fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + self[addr].1
    }

    fn normalise_args(&mut self, addr: usize, args: &[usize]) {
        match self[addr] {
            (Tag::Str, pointer) => self.normalise_args(pointer, args),
            (Tag::Func, _) => {
                for i in self.str_iterator(addr) {
                    self.normalise_args(i, args)
                }
            }
            (Tag::Lis, pointer) if pointer != CON_PTR => {
                self.normalise_args(pointer, args);
                self.normalise_args(pointer + 1, args);
            }
            (Tag::Arg, value) => self[addr].1 = args.iter().position(|i| value == *i).unwrap(),
            _ => (),
        }
    }

    fn copy_complex(&mut self, other: &impl Heap, mut addr: usize, update_addr: &mut usize) {
        addr = other.deref_addr(addr);
        match other[addr] {
            EMPTY_LIS => *update_addr = CON_PTR,
            (Tag::Str, pointer) => *update_addr = self.copy_term(other, pointer),
            (Tag::Lis, _) => *update_addr = self.copy_term(other, addr),
            _ => (),
        }
    }

    fn copy_simple(&mut self, other: &impl Heap, mut addr: usize, update_addr: &usize) {
        addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Lis, _) => self.heap_push((Tag::Lis, *update_addr)),
            (Tag::Str, _) => self.heap_push((Tag::Str, *update_addr)),
            (Tag::Ref, _) => self.heap_push((Tag::Ref, self.heap_len())),
            (_, _) => self.heap_push(other[addr]),
        };
    }

    fn copy_term(&mut self, other: &impl Heap, mut addr: usize) -> usize {
        //Assume common static heap
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Str, mut pointer) => {
                pointer = self.copy_term(other, pointer);
                self.heap_push((Tag::Str, pointer));
                self.heap_len() - 1
            }
            (Tag::Func, arity) => {
                let mut update_addr: Vec<usize> = vec![0; arity];
                for (i, a) in other.str_iterator(addr).enumerate() {
                    self.copy_complex(other, a, &mut update_addr[i])
                }
                let h = self.heap_len();
                self.heap_push((Tag::Func, arity));
                for (i, a) in other.str_iterator(addr).enumerate() {
                    self.copy_simple(other, a, &update_addr[i]);
                }
                h
            }
            (Tag::Lis, pointer) => {
                let mut update_addr: Vec<usize> = vec![0; 2];
                self.copy_complex(other, pointer, &mut update_addr[0]);
                self.copy_complex(other, pointer + 1, &mut update_addr[1]);

                let h = self.heap_len();
                self.copy_simple(other, pointer, &mut update_addr[0]);
                self.copy_simple(other, pointer + 1, &mut update_addr[1]);
                h
            }
            (Tag::Tup, len) => todo!(),
            (Tag::Set, len) => todo!(),
            (Tag::Ref, pointer) => panic!(),
            (Tag::Arg | Tag::Con | Tag::Int | Tag::Flt|Tag::Stri,_) => {
                self.heap_push(other[addr]);
                self.heap_len() - 1
            }
        }
    }

    fn term_equal(&self, mut addr1: usize, mut addr2: usize) -> bool {
        addr1 = self.deref_addr(addr1);
        addr2 = self.deref_addr(addr2);
        match (self[addr1], self[addr2]) {
            (EMPTY_LIS, EMPTY_LIS) => true,
            (EMPTY_LIS, _) => false,
            (_, EMPTY_LIS) => false,
            ((Tag::Func, a1), (Tag::Func, a2)) if a1 == a2 => self
                .str_iterator(addr1)
                .zip(self.str_iterator(addr2))
                .all(|(addr1, addr2)| self.term_equal(addr1, addr2)),
            ((Tag::Lis, p1), (Tag::Lis, p2)) => {
                self.term_equal(p1, p2) && self.term_equal(p1 + 1, p2 + 1)
            }
            ((Tag::Str, p1), (Tag::Str, p2)) => self.term_equal(p1, p2),
            ((Tag::Tup, len1), (Tag::Tup, len2)) => todo!(),
            ((Tag::Set, len1), (Tag::Set, len2)) => todo!(),
            ((Tag::Stri, i1), (Tag::Stri, i2)) =>SymbolDB::get_string(i1) == SymbolDB::get_string(i2),
            
            _ => self[addr1] == self[addr2],
        }
    }

    /**Debug function for printing formatted string of current heap state */
    fn print_heap(&self) {
        let w = 6;
        for i in 0..self.heap_len() {
            let (tag, value) = self[i];
            match tag {
                Tag::Con => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", SymbolDB::get_const(value))
                }
                Tag::Lis => {
                    if value == CON_PTR {
                        println!("[{i:3}]|{tag:w$}|{:w$}|", "[]")
                    } else {
                        println!("[{i:3}]|{tag:w$}|{value:w$}|")
                    }
                }
                Tag::Ref | Tag::Arg => {
                    println!(
                        "[{i:3}]|{tag:w$?}|{value:w$}|:({})",
                        self.term_string(i)
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
                Tag::Tup => todo!(),
                Tag::Set => todo!(),
                Tag::Stri => todo!(),
                _ => println!("[{i:3}]|{tag:w$?}|{value:w$}|"),
            };
            println!("{:-<w$}--------{:-<w$}", "", "");
        }
    }

    /**Create a string from a list */
    fn list_string(&self, addr: usize) -> String {
        if self[addr] == EMPTY_LIS {
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
            if pointer == CON_PTR {
                buffer.pop();
                break;
            }
        }
        buffer += "]";
        buffer
    }

    /**Create a string for a functor structure */
    fn func_string(&self, addr: usize) -> String {
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

    /**Create a string for a tuple*/
    fn tuple_string(&self, addr: usize) -> String {
        let mut buf = String::from("(");
        for i in 1..self[addr].1+1 {
            buf += &self.term_string(addr+i);
            buf += ",";
        }
        buf.pop();
        buf += ")";
        buf
    }

    /**Create a string for a set*/
    fn set_string(&self, addr: usize) -> String {
            let mut buf = String::from("{");
            for i in 1..self[addr].1+1 {
                buf += &self.term_string(addr+i);
                buf += ",";
            }
            buf.pop();
            buf += "}";
            buf
    }

    /** Create String to represent cell, can be recursively used to format complex structures or list */
    fn term_string(&self, addr: usize) -> String {
        // println!("[{addr}]:{:?}", self[addr]);
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Con => SymbolDB::get_const(self[addr].1).to_string(),
            Tag::Func => self.func_string(addr),
            Tag::Lis => self.list_string(addr),
            Tag::Arg => match SymbolDB::get_var(addr, self.get_id()){
                Some(symbol) => symbol.to_string(),
                None => format!("Arg_{}",self[addr].1),
            }
            Tag::Ref => match SymbolDB::get_var(self.deref_addr(addr),self.get_id()).to_owned() {
                Some(symbol) => symbol.to_string(),
                None => format!("Ref_{}",self[addr].1),
            },
            Tag::Int => {
                let value: isize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Flt => {
                let value: fsize = unsafe { mem::transmute_copy(&self[addr].1) };
                format!("{value}")
            }
            Tag::Tup => self.tuple_string(addr),
            Tag::Set => self.set_string(addr),
            Tag::Str => self.term_string(self[addr].1),
            Tag::Stri => SymbolDB::get_string(self[addr].1).to_string()
        }
    }
}

impl Heap for Vec<Cell> {
    fn heap_push(&mut self, cell: Cell) -> usize{
        let i = self.len();
        self.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        self.len()
    }
}

pub (crate) static PROG_HEAP: RwLock<Vec<Cell>> = RwLock::new(Vec::new());
