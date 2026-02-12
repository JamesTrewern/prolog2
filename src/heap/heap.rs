use std::{
    collections::HashMap,
    mem,
    ops::{Index, IndexMut, Range, RangeInclusive},
};

use super::symbol_db::SymbolDB;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    Ref,  //Query Variable
    Arg,  //Clause Variable
    Func, //Functor + tuple
    Tup,  //Tuple
    Set,  //Set
    Lis,  //List
    ELis, //Empty List
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
pub const _CON_PTR: usize = isize::MAX as usize;
pub const _FALSE: Cell = (Tag::Con, _CON_PTR);
pub const _TRUE: Cell = (Tag::Con, _CON_PTR + 1);
pub const EMPTY_LIS: Cell = (Tag::ELis, 0);

pub trait Heap: IndexMut<usize, Output = Cell> + Index<Range<usize>, Output = [Cell]> {
    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn truncate(&mut self, len: usize);

    fn get_id(&self) -> usize {
        0
    }

    fn _set_arg(&mut self, value: usize) -> usize {
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
            match self[addr] {
                (Tag::Ref, pointer) if addr == pointer => return pointer,
                (Tag::Ref, pointer) => addr = pointer,
                // (Tag::Str, pointer) => return pointer,
                _ => return addr,
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
            match self[self.deref_addr(addr + 1)] {
                (Tag::Arg | Tag::Ref, _) => (0, arity - 1),
                (Tag::Con, id) => (id, arity - 1),
                _ => panic!("Functor of structure not constant of variable"),
            }
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
    fn term_vars(&self, mut addr: usize, args: bool) -> Vec<usize> {
        addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Arg if args => vec![addr],
            Tag::Ref if !args => vec![addr],
            Tag::Lis => [
                self.term_vars(self[addr].1, args),
                self.term_vars(self[addr].1 + 1, args),
            ]
            .concat(),
            Tag::Func => self
                .str_iterator(addr)
                .map(|addr| self.term_vars(addr, args))
                .collect::<Vec<Vec<usize>>>()
                .concat(),
            _ => vec![],
        }
    }

    /** Given address to a str cell create an operator over the sub terms addresses, including functor/predicate */
    fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + self[addr].1
    }

    fn _normalise_args(&mut self, addr: usize, args: &[usize]) {
        match self[addr] {
            (Tag::Str, pointer) => self._normalise_args(pointer, args),
            (Tag::Func, _) => {
                for i in self.str_iterator(addr) {
                    self._normalise_args(i, args)
                }
            }
            (Tag::Tup, _) => todo!(),
            (Tag::Set, _) => todo!(),
            (Tag::Lis, pointer) => {
                self._normalise_args(pointer, args);
                self._normalise_args(pointer + 1, args);
            }
            (Tag::Arg, value) => self[addr].1 = args.iter().position(|i| value == *i).unwrap(),
            _ => (),
        }
    }

    fn _copy_complex(&mut self, other: &impl Heap, mut addr: usize, update_addr: &mut usize) {
        addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Str, pointer) => *update_addr = self._copy_term(other, pointer),
            (Tag::Lis, _) => *update_addr = self._copy_term(other, addr),
            _ => (),
        }
    }

    fn _copy_simple(&mut self, other: &impl Heap, mut addr: usize, update_addr: &usize) {
        addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Lis, _) => self.heap_push((Tag::Lis, *update_addr)),
            (Tag::Str, _) => self.heap_push((Tag::Str, *update_addr)),
            (Tag::Ref, _) => self.heap_push((Tag::Ref, self.heap_len())),
            (_, _) => self.heap_push(other[addr]),
        };
    }

    fn _copy_term(&mut self, other: &impl Heap, addr: usize) -> usize {
        //Assume common static heap
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Str, mut pointer) => {
                pointer = self._copy_term(other, pointer);
                self.heap_push((Tag::Str, pointer));
                self.heap_len() - 1
            }
            (Tag::Func, arity) => {
                let mut update_addr: Vec<usize> = vec![0; arity];
                for (i, a) in other.str_iterator(addr).enumerate() {
                    self._copy_complex(other, a, &mut update_addr[i])
                }
                let h = self.heap_len();
                self.heap_push((Tag::Func, arity));
                for (i, a) in other.str_iterator(addr).enumerate() {
                    self._copy_simple(other, a, &update_addr[i]);
                }
                h
            }
            (Tag::Lis, pointer) => {
                let mut update_addr: Vec<usize> = vec![0; 2];
                self._copy_complex(other, pointer, &mut update_addr[0]);
                self._copy_complex(other, pointer + 1, &mut update_addr[1]);

                let h = self.heap_len();
                self._copy_simple(other, pointer, &mut update_addr[0]);
                self._copy_simple(other, pointer + 1, &mut update_addr[1]);
                h
            }
            (Tag::Tup, _len) => todo!(),
            (Tag::Set, _len) => todo!(),
            (Tag::Ref, _pointer) => panic!(),
            (Tag::Arg | Tag::Con | Tag::Int | Tag::Flt | Tag::Stri | Tag::ELis, _) => {
                self.heap_push(other[addr]);
                self.heap_len() - 1
            }
        }
    }

    /// Copy a term from `other` heap into `self`, tracking variable identity
    /// via `ref_map`. Unbound Ref cells in `other` are mapped to fresh Ref
    /// cells in `self`; the same source Ref always maps to the same target Ref.
    /// Call with a shared `ref_map` across multiple terms to preserve variable
    /// sharing (e.g. across literals in a clause).
    fn copy_term_with_ref_map(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> usize {
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Str, pointer) => {
                let new_ptr = self.copy_term_with_ref_map(other, pointer, ref_map);
                self.heap_push((Tag::Str, new_ptr));
                self.heap_len() - 1
            }
            (Tag::Func | Tag::Tup | Tag::Set, length) => {
                // Pre-pass: recursively copy complex sub-terms
                let mut pre: Vec<Option<Cell>> = Vec::with_capacity(length);
                for i in 1..=length {
                    pre.push(self._copy_ref_map_complex(other, addr + i, ref_map));
                }
                // Lay down structure header + sub-terms
                let h = self.heap_len();
                self.heap_push((other[addr].0, length));
                for (i, pre_cell) in pre.into_iter().enumerate() {
                    match pre_cell {
                        Some(cell) => { self.heap_push(cell); }
                        None => self._copy_ref_map_simple(other, addr + 1 + i, ref_map),
                    }
                }
                h
            }
            (Tag::Lis, pointer) => {
                let head = self._copy_ref_map_complex(other, pointer, ref_map);
                let tail = self._copy_ref_map_complex(other, pointer + 1, ref_map);
                let h = self.heap_len();
                match head {
                    Some(cell) => { self.heap_push(cell); }
                    None => self._copy_ref_map_simple(other, pointer, ref_map),
                }
                match tail {
                    Some(cell) => { self.heap_push(cell); }
                    None => self._copy_ref_map_simple(other, pointer + 1, ref_map),
                }
                h
            }
            (Tag::Ref, r) if r == addr => {
                // Unbound ref — use or create mapping
                if let Some(&mapped) = ref_map.get(&addr) {
                    mapped
                } else {
                    let new_addr = self.heap_len();
                    self.heap_push((Tag::Ref, new_addr));
                    ref_map.insert(addr, new_addr);
                    new_addr
                }
            }
            (Tag::Arg | Tag::Con | Tag::Int | Tag::Flt | Tag::Stri | Tag::ELis, _) => {
                self.heap_push(other[addr]);
                self.heap_len() - 1
            }
            (tag, val) => panic!("copy_term_with_ref_map: unhandled ({tag:?}, {val})"),
        }
    }

    /// Pre-pass helper for copy_term_with_ref_map: recursively copy complex
    /// sub-terms and return the Cell to later insert, or None for simple cells.
    fn _copy_ref_map_complex(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> Option<Cell> {
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Func | Tag::Tup | Tag::Set, _) => {
                Some((Tag::Str, self.copy_term_with_ref_map(other, addr, ref_map)))
            }
            (Tag::Str, ptr) => {
                Some((Tag::Str, self.copy_term_with_ref_map(other, ptr, ref_map)))
            }
            (Tag::Lis, _) => {
                Some((Tag::Lis, self.copy_term_with_ref_map(other, addr, ref_map)))
            }
            _ => None,
        }
    }

    /// Post-pass helper for copy_term_with_ref_map: push a simple cell,
    /// handling Ref identity via ref_map.
    fn _copy_ref_map_simple(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) {
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Ref, r) if r == addr => {
                if let Some(&mapped) = ref_map.get(&addr) {
                    self.heap_push((Tag::Ref, mapped));
                } else {
                    let new_addr = self.heap_len();
                    self.heap_push((Tag::Ref, new_addr));
                    ref_map.insert(addr, new_addr);
                }
            }
            cell => { self.heap_push(cell); }
        }
    }

    fn _term_equal(&self, mut addr1: usize, mut addr2: usize) -> bool {
        addr1 = self.deref_addr(addr1);
        addr2 = self.deref_addr(addr2);
        match (self[addr1], self[addr2]) {
            (EMPTY_LIS, EMPTY_LIS) => true,
            (EMPTY_LIS, _) => false,
            (_, EMPTY_LIS) => false,
            ((Tag::Func, a1), (Tag::Func, a2)) if a1 == a2 => self
                .str_iterator(addr1)
                .zip(self.str_iterator(addr2))
                .all(|(addr1, addr2)| self._term_equal(addr1, addr2)),
            ((Tag::Lis, p1), (Tag::Lis, p2)) => {
                self._term_equal(p1, p2) && self._term_equal(p1 + 1, p2 + 1)
            }
            ((Tag::Str, p1), (Tag::Str, p2)) => self._term_equal(p1, p2),
            ((Tag::Tup, _len1), (Tag::Tup, _len2)) => todo!(),
            ((Tag::Set, _len1), (Tag::Set, _len2)) => todo!(),
            ((Tag::Stri, i1), (Tag::Stri, i2)) => {
                SymbolDB::get_string(i1) == SymbolDB::get_string(i2)
            }

            _ => self[addr1] == self[addr2],
        }
    }

    fn contains_args(&self, mut addr: usize) -> bool {
        addr = self.deref_addr(addr);
        match self[addr] {
            (Tag::Arg, _) => true,
            (Tag::Lis, ptr) => self.contains_args(ptr) || self.contains_args(ptr + 1),
            (Tag::Str, ptr) => self.contains_args(ptr),
            (Tag::Func | Tag::Set | Tag::Tup, length) => {
                (addr + 1..addr + 1 + length).any(|addr| self.contains_args(addr))
            }
            _ => false,
        }
    }

    /**Debug function for printing formatted string of current heap state */
    fn _print_heap(&self) {
        let w = 6;
        for i in 0..self.heap_len() {
            let (tag, value) = self[i];
            match tag {
                Tag::Con => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", SymbolDB::get_const(value))
                }
                Tag::Lis => {
                    if value == _CON_PTR {
                        println!("[{i:3}]|{tag:w$}|{:w$}|", "[]")
                    } else {
                        println!("[{i:3}]|{tag:w$}|{value:w$}|")
                    }
                }
                Tag::Ref | Tag::Arg => {
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|:({})", self.term_string(i))
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
        let mut buffer = "[".to_string();
        let mut pointer = self[addr].1;

        loop {
            buffer += &self.term_string(pointer);

            match self[pointer + 1].0 {
                Tag::Lis => {
                    buffer += ",";
                    pointer = self[pointer + 1].1
                }
                Tag::ELis => break,
                _ => {
                    buffer += "|";
                    buffer += &self.term_string(pointer + 1);
                    break;
                }
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
        for i in 1..self[addr].1 + 1 {
            buf += &self.term_string(addr + i);
            buf += ",";
        }
        buf.pop();
        buf += ")";
        buf
    }

    /**Create a string for a set*/
    fn set_string(&self, addr: usize) -> String {
        let mut buf = String::from("{");
        for i in 1..self[addr].1 + 1 {
            buf += &self.term_string(addr + i);
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
            Tag::ELis => "[]".into(),
            Tag::Arg => match SymbolDB::get_var(addr, self.get_id()) {
                Some(symbol) => symbol.to_string(),
                None => format!("Arg_{}", self[addr].1),
            },
            Tag::Ref => match SymbolDB::get_var(self.deref_addr(addr), self.get_id()).to_owned() {
                Some(symbol) => symbol.to_string(),
                None => format!("Ref_{}", self[addr].1),
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
            Tag::Stri => SymbolDB::get_string(self[addr].1).to_string(),
        }
    }
}

impl Heap for Vec<Cell> {
    fn heap_push(&mut self, cell: Cell) -> usize {
        let i = self.len();
        self.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        self.len()
    }
    
    fn truncate(&mut self, len: usize) {
        self.resize(len, (Tag::Ref,0));
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::heap::query_heap::QueryHeap;

    use super::{
        super::symbol_db::SymbolDB,
        {Cell, Heap, Tag, EMPTY_LIS},
    };

    #[test]
    fn encode_argument_variable() {
        let prog_cells = Arc::new(Vec::<Cell>::new());
        let mut heap = QueryHeap::new(prog_cells, None);

        let addr1 = heap._set_arg(0);
        let addr2 = heap._set_arg(1);

        assert_eq!(heap.term_string(addr1), "Arg_0");
        assert_eq!(heap.term_string(addr2), "Arg_1");
    }

    #[test]
    fn encode_ref_variable() {
        let prog_cells = Arc::new(Vec::<Cell>::new());
        let mut heap = QueryHeap::new(prog_cells, None);

        let addr1 = heap.set_ref(None);
        let addr2 = heap.set_ref(Some(addr1));

        assert_eq!(heap.term_string(addr1), "Ref_0");
        assert_eq!(heap.term_string(addr2), "Ref_0");
    }

    #[test]
    fn encode_constant() {
        let prog_cells = Arc::new(Vec::<Cell>::new());
        let mut heap = QueryHeap::new(prog_cells, None);

        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());

        let addr1 = heap.set_const(a);
        let addr2 = heap.set_const(b);

        assert_eq!(heap.term_string(addr1), "a");
        assert_eq!(heap.term_string(addr2), "b");
    }

    #[test]
    fn encode_functor() {
        let p = SymbolDB::set_const("p".into());
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Arg, 0),
            (Tag::Con, a),
        ]);

        assert_eq!(heap.term_string(0), "p(Arg_0,a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "p(f(Ref_7),a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "p((f,Ref_7),a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        
        assert_eq!(heap.term_string(0), "p({f,Ref_7},a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Lis, 5),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 7),
            (Tag::Ref, 7),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "p([f,Ref_7],a)");
    }

    #[test]
    fn encode_tuple() {
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![(Tag::Str, 1), (Tag::Tup, 2), (Tag::Arg, 0), (Tag::Con, a)]);
        assert_eq!(heap.term_string(0), "(Arg_0,a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "(f(Ref_6),a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "((f,Ref_6),a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "({f,Ref_6},a)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "([f,Ref_6],a)");
    }

    #[test]
    fn encode_list() {
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Arg, 0),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "[Arg_0,a]");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "[f(Ref_7),a]");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "[(f,Ref_7),a]");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "[{f,Ref_7},a]");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Lis, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Con, f),
            (Tag::Lis, 7),
            (Tag::Ref, 7),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "[[f,Ref_7],a]");
    }

    #[test]
    fn encode_set() {
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![(Tag::Str, 1), (Tag::Set, 2), (Tag::Arg, 0), (Tag::Con, a)]);
        assert_eq!(heap.term_string(0), "{Arg_0,a}");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "{f(Ref_6),a}");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "{(f,Ref_6),a}");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "{{f,Ref_6},a}");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "{[f,Ref_6],a}");
    }

    #[test]
    fn dereference() {
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Ref, 3)]);
        assert_eq!(heap.term_string(0), "Ref_3");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Arg, 0)]);
        assert_eq!(heap.term_string(0), "Arg_0");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Con, a)]);
        assert_eq!(heap.term_string(0), "a");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Func, 3),
            (Tag::Con, f),
            (Tag::Con, a),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "f(a,Ref_7)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Tup, 2),
            (Tag::Con, a),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "(a,Ref_6)");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Set, 2),
            (Tag::Con, a),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "{a,Ref_6}");

        let mut heap = QueryHeap::new(Arc::new(vec![]), None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "[a,Ref_6]");
    }
}
