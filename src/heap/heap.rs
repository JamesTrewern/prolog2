use std::{
    collections::HashMap,
    mem,
    ops::{Index, IndexMut, Range, RangeInclusive},
};

use super::symbol_db::SymbolDB;

/// Tag discriminant for heap cells.
///
/// Each cell on the heap is a `(Tag, usize)` pair. The tag determines how
/// the `usize` value is interpreted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    /// Query variable (self-referencing = unbound).
    Ref,
    /// Clause variable (index into substitution).
    Arg,
    /// Compound: value is the arity (following cells are functor + arguments).
    Comp,
    /// Tuple.
    Tup,
    /// Set.
    Set,
    /// List cons cell: value points to head, next cell is tail.
    Lis,
    /// Empty list.
    ELis,
    /// Constant: value is a symbol ID from the [`super::symbol_db::SymbolDB`].
    Con,
    /// Integer: value is the raw bits of an `isize`.
    Int,
    /// Float: value is the raw bits of an `fsize`.
    Flt,
    /// Indirection to a structure: value is the heap address of a Func/Tup/Set cell.
    Str,
    /// String literal: value is an index into [`super::symbol_db::SymbolDB`] strings.
    Stri,
    /// Anonymous variable: terms starting with '_' which unify with any term but don't bind
    AVar,
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// A single heap cell: a `(Tag, value)` pair.
pub type Cell = (Tag, usize);

use fsize::fsize;
pub const _CON_PTR: usize = isize::MAX as usize;
pub const _FALSE: Cell = (Tag::Con, _CON_PTR);
pub const _TRUE: Cell = (Tag::Con, _CON_PTR + 1);
pub const EMPTY_LIS: Cell = (Tag::ELis, 0);

/// Core trait for heap storage.
///
/// Implemented by both the static program heap (`Vec<Cell>`) and the
/// query-time [`super::query_heap::QueryHeap`]. Provides cell access,
/// term construction, dereferencing, and display.
pub trait Heap: IndexMut<usize, Output = Cell> + Index<Range<usize>, Output = [Cell]> {
    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn truncate(&mut self, len: usize);

    fn heap_last(&mut self) -> &mut Cell;

    fn prog_addr(&self, _addr: usize) -> bool {
        true
    }

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
            debug_assert!(
                *pointer == *src,
                "bind: tried to rebind already-bound ref at {src} (binding: {binding:?})"
            );
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

    fn walk_term_mut<T>(
        &mut self,
        addr: usize,
        accumulator: &mut T,
        operation: fn(&mut Self, usize, &mut T) -> bool,
    ) {
        let addr = self.deref_addr(addr);
        if operation(self, addr, accumulator) {
            return;
        }
        match self[addr] {
            (Tag::Lis, ptr) => {
                self.walk_term_mut(ptr, accumulator, operation);
                self.walk_term_mut(ptr + 1, accumulator, operation);
            }
            (Tag::Str, ptr) => self.walk_term_mut(ptr, accumulator, operation),
            (Tag::Comp | Tag::Tup | Tag::Set, _) => {
                for addr in self.str_iterator(addr) {
                    self.walk_term_mut(addr, accumulator, operation);
                }
            }
            _ => return,
        }
    }

    fn walk_term<T>(
        &self,
        addr: usize,
        accumulator: &mut T,
        operation: fn(&Self, usize, &mut T) -> bool,
    ) {
        let addr = self.deref_addr(addr);
        if operation(self, addr, accumulator) {
            return;
        }
        match self[addr] {
            (Tag::Lis, ptr) => {
                self.walk_term(ptr, accumulator, operation);
                self.walk_term(ptr + 1, accumulator, operation);
            }
            (Tag::Str, ptr) => self.walk_term(ptr, accumulator, operation),
            (Tag::Comp | Tag::Tup | Tag::Set, _) => {
                for addr in self.str_iterator(addr) {
                    self.walk_term(addr, accumulator, operation);
                }
            }
            _ => return,
        }
    }

    fn contains_args_opp(&self, addr: usize, acc: &mut bool) -> bool {
        let addr = self.deref_addr(addr);
        match self[addr].0 {
            Tag::Arg => {
                *acc = true;
                true
            }
            _ => false,
        }
    }

    fn contains_args(&self, addr: usize) -> bool {
        let mut acc = false;
        self.walk_term(addr, &mut acc, Self::contains_args_opp);
        false
    }

    fn term_args_op(&self, addr: usize, args: &mut Vec<usize>) -> bool {
        if self[addr].0 == Tag::Arg {
            args.push(addr);
        }
        false
    }

    fn term_refs_op(&self, addr: usize, refs: &mut Vec<usize>) -> bool {
        if self[addr].0 == Tag::Ref {
            refs.push(addr);
        }
        false
    }

    /**Collect all REF, cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    fn term_vars(&self, addr: usize, args: bool) -> Vec<usize> {
        let mut acc = Vec::new();
        if args {
            self.walk_term(addr, &mut acc, Self::term_args_op);
        } else {
            self.walk_term(addr, &mut acc, Self::term_refs_op);
        }
        acc
    }

    fn normalise_args_opp(&mut self, addr: usize, args: &mut Vec<usize>) -> bool{
        if let (Tag::Arg, id) = self[addr] {
            if let Some(pos) = args.iter().position(|i| id == *i) {
                self[addr].1 = pos;
            } else {
                let pos = args.len();
                args.push(id);
                self[addr].1 = pos;
            }
        }
        false
    }

    fn normalise_args(&mut self, addr: usize, args: &mut Vec<usize>) {
        self.walk_term_mut(addr, args, Self::normalise_args_opp);
    }

    /**Get the symbol id and arity of functor structure */
    fn str_symbol_arity(&self, mut addr: usize) -> (usize, usize) {
        addr = self.deref_addr(addr);
        if let (Tag::Str, pointer) = self[addr] {
            addr = pointer
        }
        if let (Tag::Comp, arity) = self[addr] {
            match self[self.deref_addr(addr + 1)] {
                (Tag::Arg | Tag::Ref, _) => (0, arity - 1),
                (Tag::Con, id) => (id, arity - 1),
                _ => unreachable!("str_symbol_arity: functor cell is not a constant or variable"),
            }
        } else if let (Tag::Con, symbol) = self[addr] {
            (symbol, 0)
        } else {
            unreachable!(
                "str_symbol_arity: expected structure or constant at {addr}, got {:?}",
                self[addr]
            )
        }
    }

    /** Given address to a str cell create an operator over the sub terms addresses, including functor/predicate */
    fn str_iterator(&self, addr: usize) -> RangeInclusive<usize> {
        addr + 1..=addr + self[addr].1
    }

    /// Copy a term from `other` heap into `self`, tracking variable identity
    /// via `ref_map`. Unbound Ref cells in `other` are mapped to fresh Ref
    /// cells in `self`; the same source Ref always maps to the same target Ref.
    /// Call with a shared `ref_map` across multiple terms to preserve variable
    /// sharing (e.g. across literals in a clause).
    fn copy_term(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> usize {
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Str, pointer) => {
                let new_ptr = self.copy_term(other, pointer, ref_map);
                self.heap_push((Tag::Str, new_ptr));
                self.heap_len() - 1
            }
            (Tag::Comp | Tag::Tup | Tag::Set, length) => {
                // Pre-pass: recursively copy complex sub-terms
                let mut pre: Vec<Option<Cell>> = Vec::with_capacity(length);
                for i in 1..=length {
                    pre.push(self.copy_complex(other, addr + i, ref_map));
                }
                // Lay down structure header + sub-terms
                let h = self.heap_len();
                self.heap_push((other[addr].0, length));
                for (i, pre_cell) in pre.into_iter().enumerate() {
                    match pre_cell {
                        Some(cell) => {
                            self.heap_push(cell);
                        }
                        None => self.copy_simple(other, addr + 1 + i, ref_map),
                    }
                }
                h
            }
            (Tag::Lis, pointer) => {
                let head = self.copy_complex(other, pointer, ref_map);
                let tail = self.copy_complex(other, pointer + 1, ref_map);
                let h = self.heap_len();
                match head {
                    Some(cell) => {
                        self.heap_push(cell);
                    }
                    None => self.copy_simple(other, pointer, ref_map),
                }
                match tail {
                    Some(cell) => {
                        self.heap_push(cell);
                    }
                    None => self.copy_simple(other, pointer + 1, ref_map),
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
            (tag, val) => unreachable!("copy_term_with_ref_map: unhandled cell ({tag:?}, {val})"),
        }
    }

    /// Pre-pass helper for copy_term_with_ref_map: recursively copy complex
    /// sub-terms and return the Cell to later insert, or None for simple cells.
    fn copy_complex(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) -> Option<Cell> {
        let addr = other.deref_addr(addr);
        match other[addr] {
            (Tag::Comp | Tag::Tup | Tag::Set, _) => {
                Some((Tag::Str, self.copy_term(other, addr, ref_map)))
            }
            (Tag::Str, ptr) => Some((Tag::Str, self.copy_term(other, ptr, ref_map))),
            (Tag::Lis, _) => Some((Tag::Lis, self.copy_term(other, addr, ref_map))),
            _ => None,
        }
    }

    /// Post-pass helper for copy_term_with_ref_map: push a simple cell,
    /// handling Ref identity via ref_map.
    fn copy_simple(
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
            cell => {
                self.heap_push(cell);
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
            (cell1@(Tag::Comp|Tag::Tup, _), cell2@(Tag::Comp|Tag::Tup, _)) if cell1 == cell2 => self
                .str_iterator(addr1)
                .zip(self.str_iterator(addr2))
                .all(|(addr1, addr2)| self.term_equal(addr1, addr2)),
            ((Tag::Lis, p1), (Tag::Lis, p2)) => {
                self.term_equal(p1, p2) && self.term_equal(p1 + 1, p2 + 1)
            }
            ((Tag::Str, p1), (Tag::Str, p2)) => self.term_equal(p1, p2),
            ((Tag::Set, len1), (Tag::Set, len2)) if len1 == len2 => {
                // Set equality: every element in set1 must have a match in set2
                // and vice-versa (lengths already equal, so one direction suffices
                // given no duplicates — sets are deduplicated at parse time).
                let r1 = addr1 + 1..=addr1 + len1;
                let r2 = addr2 + 1..=addr2 + len2;
                r1.clone()
                    .all(|a| r2.clone().any(|b| self.term_equal(a, b)))
            }
            ((Tag::Stri, i1), (Tag::Stri, i2)) => {
                SymbolDB::get_string(i1) == SymbolDB::get_string(i2)
            }

            _ => self[addr1] == self[addr2],
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
                Tag::Tup => println!("[{i:3}]| Tup |{value:w$}| {}", self.tuple_string(i)),
                Tag::Set => println!("[{i:3}]| Set |{value:w$}| {}", self.set_string(i)),
                Tag::Stri => println!(
                    "[{i:3}]|Stri |{value:w$}| \"{}\"",
                    SymbolDB::get_string(value)
                ),
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
        if self[addr].1 == 0 {
            return "{}".into();
        }
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
            Tag::Comp => self.func_string(addr),
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
            Tag::Stri => format!("\"{}\"", SymbolDB::get_string(self[addr].1)),
            Tag::AVar => "_".into(),
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
        self.resize(len, (Tag::Ref, 0));
    }

    fn heap_last(&mut self) -> &mut Cell {
        self.last_mut().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::heap::query_heap::QueryHeap;

    use super::{
        super::symbol_db::SymbolDB,
        {Heap, Tag, EMPTY_LIS},
    };

    #[test]
    fn encode_argument_variable() {
        let mut heap = QueryHeap::new(&[], None);

        let addr1 = heap._set_arg(0);
        let addr2 = heap._set_arg(1);

        assert_eq!(heap.term_string(addr1), "Arg_0");
        assert_eq!(heap.term_string(addr2), "Arg_1");
    }

    #[test]
    fn encode_ref_variable() {
        let mut heap = QueryHeap::new(&[], None);

        let addr1 = heap.set_ref(None);
        let addr2 = heap.set_ref(Some(addr1));

        assert_eq!(heap.term_string(addr1), "Ref_0");
        assert_eq!(heap.term_string(addr2), "Ref_0");
    }

    #[test]
    fn encode_constant() {
        let mut heap = QueryHeap::new(&[], None);

        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");

        let addr1 = heap.set_const(a);
        let addr2 = heap.set_const(b);

        assert_eq!(heap.term_string(addr1), "a");
        assert_eq!(heap.term_string(addr2), "b");
    }

    #[test]
    fn encode_functor() {
        let p = SymbolDB::set_const("p");
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Arg, 0),
            (Tag::Con, a),
        ]);

        assert_eq!(heap.term_string(0), "p(Arg_0,a)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Comp, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "p(f(Ref_7),a)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "p((f,Ref_7),a)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);

        assert_eq!(heap.term_string(0), "p({f,Ref_7},a)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Comp, 3),
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
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Arg, 0),
            (Tag::Con, a),
        ]);
        assert_eq!(heap.term_string(0), "(Arg_0,a)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Comp, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "(f(Ref_6),a)");

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Arg, 0),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "[Arg_0,a]");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Comp, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "[f(Ref_7),a]");

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Arg, 0),
            (Tag::Con, a),
        ]);
        assert_eq!(heap.term_string(0), "{Arg_0,a}");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Comp, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "{f(Ref_6),a}");

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Ref, 3),
        ]);
        assert_eq!(heap.term_string(0), "Ref_3");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Arg, 0),
        ]);
        assert_eq!(heap.term_string(0), "Arg_0");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Con, a),
        ]);
        assert_eq!(heap.term_string(0), "a");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Comp, 3),
            (Tag::Con, f),
            (Tag::Con, a),
            (Tag::Ref, 7),
        ]);
        assert_eq!(heap.term_string(0), "f(a,Ref_7)");

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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

        let mut heap = QueryHeap::new(&[], None);
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
