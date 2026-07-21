use super::{SymbolDB, TermWalk};
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    mem,
    ops::{Index, IndexMut, Range, RangeInclusive},
    todo,
};

use fsize::fsize;
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

pub const CON_PTR: usize = isize::MAX as usize;
pub const _FALSE: Cell = (Tag::Con, CON_PTR);
pub const _TRUE: Cell = (Tag::Con, CON_PTR + 1);
pub const LIS: Cell = (Tag::Lis, 0);
pub const EMPTY_LIS: Cell = (Tag::ELis, 0);
pub enum VarDeref {
    Same,           // cell at addr is not a (bound) variable — keep using addr
    Jump(usize),    // chain resolved to the term at this address
    Unbound(usize), // chain resolved to an unbound variable with this id
}

/// (from var_id, to value, true: value is another var_id | false: value is heap address)
pub type Binding = (usize, usize, bool);

/// Core trait for heap storage.
///
/// Implemented by both the static program heap (`Vec<Cell>`) and the
/// query-time [`super::query_heap::QueryHeap`]. Provides cell access,
/// term construction, dereferencing, and display.
pub trait Heap:
    Sized + IndexMut<usize, Output = Cell> + Index<Range<usize>, Output = [Cell]>
{
    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn truncate(&mut self, len: usize);

    fn heap_last(&mut self) -> &mut Cell;

    fn prog_addr(&self, _addr: usize) -> bool {
        true
    }

    fn get_id(&self, _addr: usize) -> usize {
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

    fn set_var(&mut self, var_id: Option<usize>) -> usize {
        unreachable!("Shouldn't set var in program heap");
    }

    #[inline(always)]
    fn var_deref(&self, addr: usize) -> VarDeref {
        let (Tag::Ref, mut id) = self[addr] else {
            return VarDeref::Same;
        };
        unreachable!("Should not have ref cells in program heap");
    }

    /** Update address value of ref cells affected by binding
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    fn bind(&mut self, binding: Binding) {
        unreachable!("Should not attempt to bind in program heap")
    }

    /** Reset Ref cells affected by binding to self references
     * @binding: List of (usize, usize) tuples representing heap indexes, left -> right
     */
    fn unbind(&mut self, binding: &[usize]) {
        unreachable!("Should not attempt to unbind in program heap")
    }

    fn contains_args(&self, addr: usize) -> bool {
        let mut walk = TermWalk::new(addr);
        while let Some((tag, _)) = walk.next_cell(self) {
            if tag == Tag::Arg {
                return true;
            }
        }
        false
    }

    /**Collect all REF, cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    fn term_vars(&self, addr: usize, args: bool) -> Vec<usize> {
        let mut walk = TermWalk::new(addr);
        let mut vars = Vec::new();
        while let Some((tag, value)) = walk.next_cell(self) {
            if (!args && tag == Tag::Ref) | (args && tag == Tag::Arg) {
                if !vars.contains(&value) {
                    vars.push(value);
                }
            }
        }
        vars
    }

    /**Collect all Arg, cells in structure or referenced by structure
     * If cell at addr is a reference return that cell  
     */
    fn term_args(&self, addr: usize, args: bool) -> Vec<usize> {
        let mut walk = TermWalk::new(addr);
        let mut vars = Vec::new();
        while let Some((tag, value)) = walk.next_cell(self) {
            if tag == Tag::Arg {
                if !vars.contains(&value) {
                    vars.push(value);
                }
            }
        }
        vars
    }

    ///Normalise args across multiple terms to 0 index arg ids
    fn normalise_args(&mut self, mut addr: usize, args: &mut Vec<usize>) {
        // Can ignore variable dereferencing as refs can't bind to arg terms without rebuilding
        let mut cells_left = 1;
        while cells_left > 0 {
            cells_left -= 1;
            match self[addr] {
                (Tag::Arg, arg_id) => {
                    if let Some(pos) = args.iter().position(|&arg_id2| arg_id == arg_id2) {
                        self[addr].1 = pos;
                    } else {
                        args.push(arg_id);
                    }
                }
                LIS => cells_left += 2,
                (Tag::Comp | Tag::Set | Tag::Tup, len) => cells_left += len,
                _ => (),
            }
            addr += 1;
        }
    }

    fn occurs(&self, addr: usize, var_id: usize, bound_args: &[usize]) -> bool {
        let mut walk = TermWalk::new(addr);
        while let Some(cell) = walk.next_cell(self) {
            match cell {
                (Tag::Arg, id) if bound_args.contains(&id) => {
                    return true;
                }
                (Tag::Ref, var_id2) if var_id2 == var_id => {
                    return true;
                }
                _ => (),
            }
        }
        true
    }

    /**Get the symbol id and arity of functor structure */
    fn str_symbol_arity(&self, addr: usize) -> (usize, usize) {
        if let (Tag::Comp, arity) = self[addr] {
            let functor = match self.var_deref(addr) {
                VarDeref::Same => addr,
                VarDeref::Jump(addr) => addr,
                VarDeref::Unbound(_) => return (0, arity),
            };
            match self[functor] {
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

    /// Clone term from another heap, replacing ref cells with fresh references
    /// and inlining bound references to new term
    fn clone_term_from_other(
        &mut self,
        other: &impl Heap,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) {
        let mut walk = TermWalk::new(addr);
        while let Some((tag, value)) = walk.next_cell(other) {
            if tag == Tag::Ref {
                if let Some(var_id) = ref_map.get(&value) {
                    self.heap_push((tag, *var_id));
                } else {
                    let var_id = self.set_var(None);
                    ref_map.insert(value, var_id);
                }
            } else {
                self.heap_push((tag, value));
            }
        }
    }

    /// Clone term replacing ref cells with fresh references
    /// and inlining bound references to new term
    fn clone_term(
        &mut self,
        addr: usize,
        ref_map: &mut HashMap<usize, usize>,
    ) {
        let mut walk = TermWalk::new(addr);
        while let Some((tag, value)) = walk.next_cell(self) {
            if tag == Tag::Ref {
                if let Some(var_id) = ref_map.get(&value) {
                    self.heap_push((tag, *var_id));
                } else {
                    let var_id = self.set_var(None);
                    ref_map.insert(value, var_id);
                }
            } else {
                self.heap_push((tag, value));
            }
        }
    }

    /// Naively copy cells from a term, with no dereferencing 
    fn copy_term(&mut self, mut addr: usize){
        // Can ignore variable dereferencing as refs can't bind to arg terms without rebuilding
        let mut cells_left = 1;
        while cells_left > 0 {
            cells_left -= 1;
            self.heap_push(self[addr]);
            match self[addr] {
                LIS => cells_left += 2,
                (Tag::Comp | Tag::Set | Tag::Tup, len) => cells_left += len,
                _ => (),
            }
            addr += 1;
        }
    }

    fn term_equal(&self, addr1: usize, addr2: usize) -> bool {
        let (mut walk1, mut walk2) = (TermWalk::new(addr1), TermWalk::new(addr2));
        loop {
            let (Some(cell1), Some(cell2)) = (walk1.next_cell(self), walk2.next_cell(self)) else {
                return true;
            };

            match (cell1, cell2) {
                ((Tag::Set, len1), (Tag::Set, len2)) if len1 == len2 => {
                    // Set equality: every element in set1 must have a match in set2
                    // and vice-versa (lengths already equal, so one direction suffices
                    // given no duplicates — sets are deduplicated at parse time).
                    let r1 = addr1 + 1..=addr1 + len1;
                    let r2 = addr2 + 1..=addr2 + len2;
                    if !r1
                        .clone()
                        .all(|a| r2.clone().any(|b| self.term_equal(a, b)))
                    {
                        return false;
                    }
                    walk1.skip_addrs(len1);
                    walk2.skip_addrs(len1);
                }
                ((Tag::Stri, i1), (Tag::Stri, i2)) => {
                    if *SymbolDB::get_string(i1) != *SymbolDB::get_string(i2) {
                        return false;
                    }
                }
                _ => {
                    if self[addr1] != self[addr2] {
                        return false;
                    }
                }
            }
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
                Tag::Lis => println!("[{i:3}]|{tag:w$}|{value:w$}|"),
                Tag::ELis => println!("[{i:3}]|{tag:w$}|{:w$}|", "[]"),
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
                Tag::Tup => println!("[{i:3}]| Tup |{value:w$}| {}", self.term_string(i)),
                Tag::Set => println!("[{i:3}]| Set |{value:w$}| {}", self.term_string(i)),
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
    fn list_string(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        write!(buf, "[")?;
        loop {
            *addr += 1;
            self.term_string_rec(addr, buf)?;
            *addr += 1;
            match self[*addr].0 {
                Tag::Lis => {
                    write!(buf, ",")?;
                }
                Tag::ELis => break,
                _ => {
                    write!(buf, "|")?;
                    self.term_string_rec(addr, buf)?;
                    break;
                }
            }
        }
        write!(buf, "]")?;
        Ok(())
    }

    /**Create a string for a compound structure */
    fn comp_string(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        let len = self[*addr].1;
        *addr += 1;
        self.term_string_rec(addr, buf)?;
        write!(buf, "(")?;
        for _ in 1..len {
            *addr += 1;
            self.term_string_rec(addr, buf)?;
            write!(buf, ",")?;
        }

        buf.pop();
        write!(buf, ")")?;
        Ok(())
    }

    /**Create a string for a tuple*/
    fn tuple_string(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        let len = self[*addr].1;
        write!(buf, "(")?;
        for _ in 0..len {
            *addr += 1;
            self.term_string_rec(addr, buf)?;
            write!(buf, ",")?;
        }

        buf.pop();
        write!(buf, ")")?;
        Ok(())
    }

    /**Create a string for a set*/
    fn set_string(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        let len = self[*addr].1;
        if len == 0 {
            buf.write_str("{}")?;
            return Ok(());
        }

        buf.write_str("{")?;
        for _ in 0..len {
            *addr += 1;
            self.term_string_rec(addr, buf)?;
            buf.write_str(",")?;
        }
        buf.pop();
        buf.write_str("}")?;
        Ok(())
    }

    /** Create String to represent cell, can be recursively used to format complex structures or list */
    fn term_string_rec(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        // println!("[{addr}]:{:?}", self[addr]);
        match self[*addr].0 {
            Tag::Con => buf.write_str(&SymbolDB::get_const(self[*addr].1)),
            Tag::Comp => self.comp_string(addr, buf),
            Tag::Lis => self.list_string(addr, buf),
            Tag::ELis => write!(buf, "[]"),
            Tag::Arg => match SymbolDB::get_var(*addr, self.get_id(*addr)) {
                Some(symbol) => buf.write_str(&symbol),
                None => write!(buf, "Arg_{}", self[*addr].1),
            },
            Tag::Ref => match self.var_deref(*addr) {
                VarDeref::Jump(mut ref_addr) => self.term_string_rec(&mut ref_addr, buf),
                VarDeref::Unbound(var_id) => {
                    match SymbolDB::get_var(var_id, self.get_id(*addr)).to_owned() {
                        Some(symbol) => buf.write_str(&symbol),
                        None => write!(buf, "Ref_{}", self[*addr].1),
                    }
                }
                VarDeref::Same => {
                    unreachable!("Ref should not be able to return same (should be unbound)")
                }
            },
            Tag::Int => {
                let value: isize = unsafe { mem::transmute_copy(&self[*addr].1) };
                write!(buf, "{value}")
            }
            Tag::Flt => {
                let value: fsize = unsafe { mem::transmute_copy(&self[*addr].1) };
                write!(buf, "{value}")
            }
            Tag::Tup => self.tuple_string(addr, buf),
            Tag::Set => self.set_string(addr, buf),
            Tag::Stri => write!(buf, "\"{}\"", SymbolDB::get_string(self[*addr].1)),
            Tag::AVar => write!(buf, "_"),
        }
    }

    fn term_string(&self, mut addr: usize) -> String {
        let mut buf = String::new();
        self.term_string_rec(&mut addr, &mut buf).unwrap();
        buf
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
    use std::collections::HashMap;

    use crate::heap::query_heap::QueryHeap;

    use super::{
        super::symbol_db::SymbolDB,
        {Heap, Tag, EMPTY_LIS, LIS},
    };

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
            (Tag::Comp, 3),
            (Tag::Con, f),
            (Tag::Con, a),
            (Tag::Ref, 6),
        ]);
        assert_eq!(heap.term_string(0), "f(a,Ref_6)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Tup, 2),
            (Tag::Con, a),
            (Tag::Ref, 5),
        ]);
        assert_eq!(heap.term_string(0), "(a,Ref_5)");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Set, 2),
            (Tag::Con, a),
            (Tag::Ref, 5),
        ]);
        assert_eq!(heap.term_string(0), "{a,Ref_5}");

        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            LIS,
            (Tag::Con, a),
            LIS,
            (Tag::Ref, 6),
            EMPTY_LIS,
        ]);
        assert_eq!(heap.term_string(0), "[a,Ref_6]");
    }

    #[test]
    fn var_deref() {
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![
            (Tag::Ref, 0),
            (Tag::Ref, 2),
            (Tag::Con, a),
            (Tag::Ref, 4),
            (Tag::Ref, 5),
            (Tag::Con, a),
        ]);
        todo!();
    }

    #[test]
    fn clone_term() {
        let a = SymbolDB::set_const("a");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");

        //Test simple
        let mut heap = QueryHeap::new(&[], None);
        let mut other = QueryHeap::new(&[], None);
        other.cells.extend(vec![
            (Tag::Comp, 3),
            (Tag::Con, f),
            (Tag::Con, a),
            (Tag::Arg, 0),
        ]);
        heap.clone_term_from_other(&other, 0, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Tag::Comp, 3), (Tag::Con, f), (Tag::Con, a), (Tag::Arg, 0),]
        );

        //Test ref reasingment
        let mut heap = QueryHeap::new(&[], None);
        heap.cells.extend(vec![EMPTY_LIS, EMPTY_LIS, EMPTY_LIS]);
        let mut other = QueryHeap::new(&[], None);
        other.cells.extend(vec![
            (Tag::Tup, 4),
            (Tag::Ref, 2),
            (Tag::Ref, 2),
            (Tag::Ref, 2),
            (Tag::Ref, 4),
        ]);
        heap.clone_term_from_other(&other, 0, &mut HashMap::new());
        assert_eq!(
            &heap.cells[3..],
            &[
                (Tag::Tup, 4),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
                (Tag::Ref, 7),
            ]
        );

        // Ref bound to simple term
        let mut heap = QueryHeap::new(&[], None);
        let mut other = QueryHeap::new(&[], None);
        other.cells.extend(vec![
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Ref, 3),
            (Tag::Ref, 0),
            (Tag::Tup, 2),
            (Tag::Ref, 0),
            (Tag::Ref, 5),
        ]);
        heap.clone_term_from_other(&other, 1, &mut HashMap::new());
        heap.clone_term_from_other(&other, 4, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[
                (Tag::Tup, 2),
                (Tag::Con, a),
                (Tag::Con, a),
                (Tag::Tup, 2),
                (Tag::Con, a),
                (Tag::Con, a),
            ]
        );

        // Ref bound to complex term
        let mut heap = QueryHeap::new(&[], None);
        let mut other = QueryHeap::new(&[], None);
        other.cells.extend(vec![
            (Tag::Comp, 2), // 0
            (Tag::Con, f),  // 1
            (Tag::Con, a),  // 2
            (Tag::Comp, 2), // 3
            (Tag::Con, p),  // 4
            (Tag::Ref, 0),  // 5
            (Tag::Comp, 2), // 6
            (Tag::Con, p),  // 7
            (Tag::Ref, 3),  // 8
        ]);
        heap.clone_term_from_other(&other, 6, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[
                (Tag::Comp, 2),
                (Tag::Con, p),
                (Tag::Comp, 2),
                (Tag::Con, p),
                (Tag::Comp, 2),
                (Tag::Con, f),
                (Tag::Con, a),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let mut other = QueryHeap::new(&[], None);
        other.cells.extend(vec![
            LIS,            // 0
            (Tag::Con, f),  // 1
            (Tag::Con, a),  // 2
            LIS,            // 3
            (Tag::Con, p),  // 4
            (Tag::Ref, 0),  // 5
            (Tag::Comp, 2), // 6
            (Tag::Con, p),  // 7
            (Tag::Ref, 3),  // 8
        ]);
        heap.clone_term_from_other(&other, 6, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[
                (Tag::Comp, 2),
                (Tag::Con, p),
                LIS,
                (Tag::Con, p),
                LIS,
                (Tag::Con, f),
                (Tag::Con, a),
            ]
        );
    }

    #[test]
    fn normalise_args() {
        let mut norm_args_map = Vec::new();
        let mut heap = vec![
            (Tag::Comp, 3),
            (Tag::Arg, 2),
            (Tag::Arg, 4),
            (Tag::Arg, 1),
            (Tag::Comp, 1),
            LIS,
            (Tag::Arg, 1),
            LIS,
            (Tag::Arg, 4),
            LIS,
            (Tag::Arg, 2),
            EMPTY_LIS,
        ];
        heap.normalise_args(0, &mut norm_args_map);
        heap.normalise_args(4, &mut norm_args_map);

        assert_eq!(
            &heap,
            &[
                (Tag::Comp, 3),
                (Tag::Arg, 0),
                (Tag::Arg, 1),
                (Tag::Arg, 2),
                (Tag::Comp, 1),
                LIS,
                (Tag::Arg, 2),
                LIS,
                (Tag::Arg, 1),
                LIS,
                (Tag::Arg, 0),
                EMPTY_LIS
            ]
        )
    }
}
