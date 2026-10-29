use super::{
    SymbolDB,
    Tag::*,
    TermWalk,
    VarBind::{self, *},
    Walk,
};
use std::{
    collections::HashMap,
    fmt::Write,
    mem,
    ops::{Index, IndexMut, Range, RangeFrom},
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
    Var,
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

pub const LIS: Cell = (Lis, 0);
pub const EMPTY_LIS: Cell = (ELis, 0);

/// Core trait for heap storage.
///
/// Implemented by both the static program heap (`Vec<Cell>`) and the
/// query-time [`super::query_heap::QueryHeap`]. Provides cell access,
/// term construction, dereferencing, and display.
pub trait Heap:
    Sized
    + IndexMut<usize, Output = Cell>
    + Index<Range<usize>, Output = [Cell]>
    + Index<RangeFrom<usize>>
{
    /// Reset Ref cells affected by binding to self references
    /// @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    fn unbind(&mut self, binding: &[usize]);

    /// Update address value of ref cells affected by binding
    /// @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    fn bind(&mut self, var_id: usize, binding: VarBind);

    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn heap_last(&mut self) -> &mut Cell;

    fn set_var(&mut self, var_id: Option<usize>) -> usize;

    fn bound(&self, var_id: usize) -> Option<VarBind>;

    /// Return VarBind for a given var_id
    /// If var_id unbound return Unbound
    /// If var_id bound follow binding chains
    /// Return either last unbound var as Var(var_id)
    /// Or return Addr(addr)
    fn var_deref(&self, var_id: usize) -> VarBind;

    fn get_deref_cell(&self, addr: usize) -> Cell {
        if let (Var, var_id) = self[addr] {
            match self.var_deref(var_id) {
                VarId(var_id) => (Var, var_id),
                Addr(addr) => self[addr],
            }
        } else {
            self[addr]
        }
    }

    fn prog_addr(&self, _addr: usize) -> bool {
        true
    }

    fn get_id(&self, _addr: usize) -> usize {
        0
    }

    fn _set_arg(&mut self, value: usize) -> usize {
        //If no address provided set addr to current heap len
        self.heap_push((Arg, value));
        return self.heap_len() - 1;
    }

    fn set_const(&mut self, id: usize) -> usize {
        let h = self.heap_len();
        self.heap_push((Con, id));
        h
    }

    fn contains_args(&self, addr: usize) -> bool {
        let mut walk = TermWalk::new(addr);
        while let Some((tag, _)) = walk.next_cell(self) {
            if tag == Arg {
                return true;
            }
        }
        false
    }

    /// Collect all Ref or Arg ids in term
    /// @ args: true -> collect args, false -> collect refss
    fn term_vars(&self, addr: usize, args: bool) -> Vec<usize> {
        let mut walk = TermWalk::new(addr);
        let mut vars = Vec::new();
        while let Some((tag, value)) = walk.next_cell(self) {
            if (!args && tag == Var) | (args && tag == Arg) {
                if !vars.contains(&value) {
                    vars.push(value);
                }
            }
        }
        vars
    }

    fn occurs(&self, addr: usize, var_id: usize, bound_args: &[usize]) -> bool {
        let mut walk = TermWalk::new(addr);
        while let Some(cell) = walk.next_cell(self) {
            match cell {
                (Arg, id) if bound_args.contains(&id) => {
                    return true;
                }
                (Var, var_id2) if var_id2 == var_id => {
                    return true;
                }
                _ => (),
            }
        }
        true
    }

    ///Get the symbol id and arity of functor structure (Comp)
    fn symbol_arity(&self, addr: usize) -> (usize, usize) {
        if let (Comp, arity) = self[addr] {
            let mut functor = self[addr + 1];
            if functor.0 == Var {
                let Addr(addr) = self.var_deref(functor.1) else {
                    return (0, arity - 1);
                };
                functor = self[addr];
            }
            match functor {
                (Arg, _) => (0, arity - 1),
                (Con, id) => (id, arity - 1),
                _ => unreachable!("str_symbol_arity: functor cell is not a constant or variable"),
            }
        } else if let (Con, symbol) = self[addr] {
            (symbol, 0)
        } else {
            unreachable!(
                "str_symbol_arity: expected structure or constant at {addr}, got {:?}",
                self[addr]
            )
        }
    }

    fn pred_var(&self, addr: usize) -> Option<usize> {
        if self[addr].0 != Comp {
            return None;
        }
        let (Var, var_id) = self[addr + 1] else {
            return None;
        };
        match self.var_deref(var_id) {
            VarId(var_id) => Some(var_id),
            Addr(_) => None,
        }
    }

    /// Given address to a str cell create an operator over the sub terms addresses, including functor/predicate
    fn str_args(&self, mut addr: usize) -> Vec<usize> {
        let len = self[addr].1;
        let mut args = Vec::with_capacity(len);
        addr += 1;
        for _ in 0..len {
            args.push(addr);
            addr += self.term_len(addr);
        }
        args
    }

    /// Find length of term on heap, ignoring dereference jumps.
    /// This length can be used to skip over subterms
    fn term_len(&self, mut addr: usize) -> usize {
        let mut term_len = 0;
        let mut cells_left = 1;
        while cells_left > 0 {
            match self[addr] {
                (Comp | Tup | Set, len) => cells_left += len,
                LIS => cells_left += 2,
                _ => (),
            }
            cells_left -= 1;
            term_len += 1;
            addr += 1;
        }
        term_len
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
            if tag == Var {
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
    fn clone_term(&mut self, addr: usize, ref_map: &mut HashMap<usize, usize>) {
        let mut walk = TermWalk::new(addr);
        while let Some((tag, value)) = walk.next_cell(self) {
            if tag == Var {
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
    fn copy_term(&mut self, mut addr: usize) {
        // Can ignore variable dereferencing as refs can't bind to arg terms without rebuilding
        let mut cells_left = 1;
        while cells_left > 0 {
            cells_left -= 1;
            self.heap_push(self[addr]);
            match self[addr] {
                LIS => cells_left += 2,
                (Comp | Set | Tup, len) => cells_left += len,
                _ => (),
            }
            addr += 1;
        }
    }

    /// Are the terms at these two addresses structurally equal?
    ///
    /// Both terms are walked in step with [`TermWalk`], which normalises
    /// variables as it goes: one bound to a term is followed into it, and one
    /// aliased to another unbound variable is reported under its
    /// representative. That matters because variable bindings live in the
    /// registers rather than in the cells, so two cells naming the same
    /// variable -- `(Var, i)` where `i` is aliased to `j`, against
    /// `(Var, j)` -- are only equal once the walk has resolved them.
    ///
    /// Sets are the exception to walking in step: their elements are
    /// unordered, so they cannot be compared position by position. Each
    /// element is matched against any element of the other set, and both
    /// subterms are then consumed so the surrounding walk resumes after them.
    fn term_equal(&self, addr1: usize, addr2: usize) -> bool {
        if addr1 == addr2 {
            return true;
        }

        let (mut walk1, mut walk2) = (TermWalk::new(addr1), TermWalk::new(addr2));
        loop {
            match (
                walk1.next_cell_with_addr(self),
                walk2.next_cell_with_addr(self),
            ) {
                (None, None) => return true,

                // Equal sizes only; a size mismatch falls to the cell
                // comparison below and fails there.
                (Some((set1, (Set, len1))), Some((set2, (Set, len2)))) if len1 == len2 => {
                    if !sets_equal(self, set1, set2) {
                        return false;
                    }
                    consume_subterm(&mut walk1, self);
                    consume_subterm(&mut walk2, self);
                }

                // Equal text may have been interned twice under different
                // indices, so compare the content.
                (Some((_, (Stri, index1))), Some((_, (Stri, index2)))) => {
                    if *SymbolDB::get_string(index1) != *SymbolDB::get_string(index2) {
                        return false;
                    }
                }

                (Some((_, cell1)), Some((_, cell2))) => {
                    if cell1 != cell2 {
                        return false;
                    }
                }

                // One term ran out before the other.
                _ => return false,
            }
        }
    }

    ///Debug function for printing formatted string of current heap state
    fn _print_heap(&self) {
        self._print_heap_from(0);
    }

    ///Debug function for printing formatted string of current heap state
    fn _print_heap_from(&self, from: usize) {
        let w = 6;
        for i in from..self.heap_len() {
            let (tag, value) = self[i];
            match tag {
                Con => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", SymbolDB::get_const(value))
                }
                Lis => println!("[{i:3}]|{tag:w$}|{value:w$}|"),
                ELis => println!("[{i:3}]|{tag:w$}|{:w$}|", "[]"),
                Var | Arg => {
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|:({})", self.term_string(i))
                }
                Int => {
                    let value: isize = unsafe { mem::transmute_copy(&value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                Flt => {
                    let value: fsize = unsafe { mem::transmute_copy(&value) };
                    println!("[{i:3}]|{tag:w$?}|{value:w$}|")
                }
                Tup => println!("[{i:3}]| Tup |{value:w$}| {}", self.term_string(i)),
                Set => println!("[{i:3}]| Set |{value:w$}| {}", self.term_string(i)),
                Stri => println!(
                    "[{i:3}]|Stri |{value:w$}| \"{}\"",
                    SymbolDB::get_string(value)
                ),
                _ => println!("[{i:3}]|{tag:w$?}|{value:w$}|"),
            };
            println!("{:-<w$}--------{:-<w$}", "", "");
        }
    }

    ///Create a string from a list
    fn list_string(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        write!(buf, "[")?;
        loop {
            *addr += 1;
            self.term_string_rec(addr, buf)?;
            *addr += 1;
            match self[*addr].0 {
                Lis => {
                    write!(buf, ",")?;
                }
                ELis => break,
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

    ///Create a string for a compound structure
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

    ///Create a string for a tuple
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

    ///Create a string for a set
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

    /// Create String to represent cell, can be recursively used to format complex structures or list
    fn term_string_rec(&self, addr: &mut usize, buf: &mut String) -> Result<(), std::fmt::Error> {
        // println!("[{addr}]:{:?}", self[addr]);
        match self[*addr].0 {
            Con => buf.write_str(&SymbolDB::get_const(self[*addr].1)),
            Comp => self.comp_string(addr, buf),
            Lis => self.list_string(addr, buf),
            ELis => write!(buf, "[]"),
            Arg => match SymbolDB::get_var(*addr, self.get_id(*addr)) {
                Some(symbol) => buf.write_str(&symbol),
                None => write!(buf, "Arg_{}", self[*addr].1),
            },
            Var => match self.var_deref(self[*addr].1) {
                Addr(mut ref_addr) => self.term_string_rec(&mut ref_addr, buf),
                VarId(var_id) => match SymbolDB::get_var(var_id, self.get_id(*addr)).to_owned() {
                    Some(symbol) => buf.write_str(&symbol),
                    // Name the *representative*, not the cell. Unifying two
                    // free variables aliases one to the other without binding
                    // either to a term, so several distinct cell ids can
                    // denote a single variable. Printing the cell id gives
                    // that one variable several names, which matters most for
                    // invented predicates: an invented predicate reached
                    // through an alias would render as a second, apparently
                    // unrelated predicate.
                    None => write!(buf, "Ref_{var_id}"),
                },
            },
            Int => {
                let value: isize = unsafe { mem::transmute_copy(&self[*addr].1) };
                write!(buf, "{value}")
            }
            Flt => {
                let value: fsize = unsafe { mem::transmute_copy(&self[*addr].1) };
                write!(buf, "{value}")
            }
            Tup => self.tuple_string(addr, buf),
            Set => self.set_string(addr, buf),
            Stri => write!(buf, "\"{}\"", SymbolDB::get_string(self[*addr].1)),
            AVar => write!(buf, "_"),
        }
    }

    fn term_string(&self, mut addr: usize) -> String {
        let mut buf = String::new();
        self.term_string_rec(&mut addr, &mut buf).unwrap();
        buf
    }
}

/// Do two sets hold the same elements, in any order?
///
/// Equal sizes plus a match for every element of the first is enough, since
/// a set holds no duplicates.
fn sets_equal(heap: &impl Heap, addr1: usize, addr2: usize) -> bool {
    let (elements1, elements2) = (heap.str_args(addr1), heap.str_args(addr2));
    elements1
        .iter()
        .all(|&a| elements2.iter().any(|&b| heap.term_equal(a, b)))
}

/// Step `walk` past the subterm whose header it just returned.
///
/// [`TermWalk::sub_walk`] takes the subterm's cells off the parent frame and
/// hands back a walk over them; draining that walk leaves the parent pointing
/// at whatever follows. Needed because the subterm's cell count is not the
/// element count recorded in its header once its elements are themselves
/// multi-cell.
fn consume_subterm(walk: &mut TermWalk, heap: &impl Heap) {
    let mut sub_walk = walk.sub_walk(heap);
    while sub_walk.next_cell(heap).is_some() {}
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

    fn heap_last(&mut self) -> &mut Cell {
        self.last_mut().unwrap()
    }

    fn set_var(&mut self, _: Option<usize>) -> usize {
        unreachable!("Shouldn't set var in program heap");
    }

    fn bound(&self, _var_id: usize) -> Option<VarBind> {
        unreachable!("Should not consult program heap for variable binding")
    }

    fn var_deref(&self, _: usize) -> VarBind {
        unreachable!("no vars to deref in program heap")
    }

    fn bind(&mut self, _: usize, _: VarBind) {
        unreachable!("Should not attempt to bind in program heap")
    }

    fn unbind(&mut self, _: &[usize]) {
        unreachable!("Should not attempt to unbind in program heap")
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::heap::{
        query_heap::QueryHeap,
        VarBind::{Addr, VarId},
        VarReg,
    };

    use super::{
        super::symbol_db::SymbolDB,
        {Heap, Tag::*, EMPTY_LIS, LIS},
    };

    #[test]
    fn var_deref() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_regs.extend_from_slice(&[
            VarId(1).into(),
            VarId(2).into(),
            Addr(3).into(),
            VarId(4).into(),
            VarId(5).into(),
            VarReg::UNBOUND,
        ]);

        assert_eq!(Addr(3), heap.var_deref(0));
        assert_eq!(Addr(3), heap.var_deref(1));
        assert_eq!(Addr(3), heap.var_deref(2));
        assert_eq!(VarId(5), heap.var_deref(3));
        assert_eq!(VarId(5), heap.var_deref(4));
        assert_eq!(VarId(5), heap.var_deref(5));
    }

    #[test]
    fn dereference() {
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.var_regs.extend_from_slice(&[
            VarId(1).into(),
            VarId(2).into(),
            Addr(3).into(),
            VarReg::UNBOUND,
        ]);

        heap.cells = vec![(Var, 0), (Var, 1), (Var, 2), (Var, 3)];
        assert_eq!(heap.term_string(0), "Ref_3");

        heap.cells = vec![(Var, 0), (Var, 1), (Var, 2), (Arg, 0)];
        assert_eq!(heap.term_string(0), "Arg_0");

        heap.cells = vec![(Var, 0), (Var, 1), (Var, 2), (Con, a)];
        assert_eq!(heap.term_string(0), "a");

        heap.cells = vec![
            (Var, 0),
            (Var, 1),
            (Var, 2),
            (Comp, 3),
            (Con, f),
            (Con, a),
            (Var, 3),
        ];
        assert_eq!(heap.term_string(0), "f(a,Ref_3)");

        heap.cells = vec![(Var, 0), (Var, 1), (Var, 2), (Tup, 2), (Con, a), (Var, 3)];
        assert_eq!(heap.term_string(0), "(a,Ref_3)");

        heap.cells = vec![(Var, 0), (Var, 1), (Var, 2), (Set, 2), (Con, a), (Var, 3)];
        assert_eq!(heap.term_string(0), "{a,Ref_3}");

        heap.cells = vec![
            (Var, 0),
            (Var, 1),
            (Var, 2),
            LIS,
            (Con, a),
            LIS,
            (Var, 3),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "[a,Ref_3]");
    }

    #[test]
    fn clone_term() {
        let a = SymbolDB::set_const("a");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");

        //Test simple
        let mut heap = QueryHeap::new(&[], None);
        let mut other = QueryHeap::new(&[], None);
        other.cells = vec![(Comp, 3), (Con, f), (Con, a), (Arg, 0)];
        heap.clone_term_from_other(&other, 0, &mut HashMap::new());
        assert_eq!(&heap.cells, &[(Comp, 3), (Con, f), (Con, a), (Arg, 0),]);

        //Test ref reasingment
        heap.cells.clear();
        heap.var_regs.clear();
        other.cells = vec![(Tup, 4), (Var, 0), (Var, 1), (Var, 2), (Var, 3)];
        other.var_regs = vec![
            VarId(1).into(),
            VarId(2).into(),
            VarReg::UNBOUND,
            VarReg::UNBOUND,
        ];
        heap.clone_term_from_other(&other, 0, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Tup, 4), (Var, 0), (Var, 0), (Var, 0), (Var, 1),]
        );

        // Ref bound to simple term
        heap.cells.clear();
        heap.var_regs.clear();
        //(a,a)
        other.cells = vec![
            (Con, a),
            (Tup, 2),
            (Var, 0),
            (Var, 1),
            (Tup, 2),
            (Var, 2),
            (Var, 3),
        ];
        other.var_regs = vec![
            VarId(1).into(),
            Addr(0).into(),
            VarId(3).into(),
            Addr(0).into(),
        ];
        heap.clone_term_from_other(&other, 1, &mut HashMap::new());
        heap.clone_term_from_other(&other, 4, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Tup, 2), (Con, a), (Con, a), (Tup, 2), (Con, a), (Con, a),]
        );

        // Ref bound to complex term
        heap.cells.clear();
        heap.var_regs.clear();
        other.cells = vec![
            (Comp, 2), // 0
            (Con, f),  // 1
            (Con, a),  // 2
            (Comp, 2), // 3
            (Con, p),  // 4
            (Var, 0),  // 5
            (Comp, 2), // 6
            (Con, p),  // 7
            (Var, 1),  // 8
        ];
        other.var_regs = vec![Addr(0).into(), Addr(3).into()];
        heap.clone_term_from_other(&other, 6, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[
                (Comp, 2),
                (Con, p),
                (Comp, 2),
                (Con, p),
                (Comp, 2),
                (Con, f),
                (Con, a),
            ]
        );

        heap.cells.clear();
        heap.var_regs.clear();
        // p([p|[f|a]])
        other.cells = vec![
            LIS,       // 0
            (Con, f),  // 1
            (Con, a),  // 2
            LIS,       // 3
            (Con, p),  // 4
            (Var, 0),  // 5
            (Comp, 2), // 6
            (Con, p),  // 7
            (Var, 1),  // 8
        ];
        other.var_regs = vec![Addr(0).into(), Addr(3).into()];
        heap.clone_term_from_other(&other, 6, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Comp, 2), (Con, p), LIS, (Con, p), LIS, (Con, f), (Con, a),]
        );
    }

    #[test]
    fn str_symbol_arity() {
        let p = SymbolDB::set_const("p");
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);

        //p(a)
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a)];
        assert_eq!(heap.symbol_arity(0), (p, 1));

        //p
        heap.cells = vec![(Con, p)];
        assert_eq!(heap.symbol_arity(0), (p, 0));

        // p(f(a),f(a))
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            (Con, a),
            (Comp, 2),
            (Con, f),
            (Con, a),
        ];
        assert_eq!(heap.symbol_arity(0), (p, 2));
        assert_eq!(heap.symbol_arity(2), (f, 1));
        assert_eq!(heap.symbol_arity(5), (f, 1));

        //Arg
        heap.cells = vec![(Comp, 2), (Arg, 0), (Con, a)];
        assert_eq!(heap.symbol_arity(0), (0, 1));

        //Var chain to con
        heap.cells = vec![(Con, p), (Comp, 2), (Var, 0), (Var, 1)];
        heap.var_regs = vec![VarId(1).into(), Addr(0).into()];
        assert_eq!(heap.symbol_arity(1), (p, 1));

        //Unbound var + chain to unbound var
        heap.cells = vec![(Comp, 2), (Var, 0), (Con, a), (Comp, 2), (Var, 1), (Var, 2)];
        heap.var_regs = vec![VarReg::UNBOUND, VarId(2).into(), VarReg::UNBOUND];
        assert_eq!(heap.symbol_arity(0), (0, 1));
        assert_eq!(heap.symbol_arity(3), (0, 1));
    }
}

#[cfg(test)]
mod term_equal_tests {
    use crate::heap::{Cell, Heap, QueryHeap, SymbolDB, Tag::*, VarBind, VarReg, EMPTY_LIS, LIS};

    fn con(name: &str) -> Cell {
        (Con, SymbolDB::set_const(name))
    }

    /// Lay `cells` on a fresh heap and return the address they start at.
    fn push(heap: &mut QueryHeap, cells: &[Cell]) -> usize {
        let addr = heap.heap_len();
        for &cell in cells {
            heap.heap_push(cell);
        }
        addr
    }

    fn heap() -> QueryHeap<'static> {
        QueryHeap::new(&[], None)
    }

    #[test]
    fn atoms_compare_by_symbol() {
        let mut heap = heap();
        let a = push(&mut heap, &[con("a")]);
        let same = push(&mut heap, &[con("a")]);
        let other = push(&mut heap, &[con("b")]);

        assert!(heap.term_equal(a, same));
        assert!(!heap.term_equal(a, other));
    }

    /// The case that used to be wrong: two compounds of the same arity were
    /// reported equal whatever their functors or arguments, because only the
    /// header cells were ever compared.
    #[test]
    fn compounds_of_equal_arity_compare_their_contents() {
        let mut heap = heap();
        let f_a = push(&mut heap, &[(Comp, 2), con("f"), con("a")]);
        let f_a_again = push(&mut heap, &[(Comp, 2), con("f"), con("a")]);
        let g_b = push(&mut heap, &[(Comp, 2), con("g"), con("b")]);
        let f_b = push(&mut heap, &[(Comp, 2), con("f"), con("b")]);

        assert!(heap.term_equal(f_a, f_a_again));
        assert!(!heap.term_equal(f_a, g_b), "different functor");
        assert!(!heap.term_equal(f_a, f_b), "different argument");
    }

    #[test]
    fn compounds_of_different_arity_differ() {
        let mut heap = heap();
        let f_a = push(&mut heap, &[(Comp, 2), con("f"), con("a")]);
        let f_a_b = push(&mut heap, &[(Comp, 3), con("f"), con("a"), con("b")]);
        assert!(!heap.term_equal(f_a, f_a_b));
    }

    #[test]
    fn nested_compounds_compare_all_the_way_down() {
        let mut heap = heap();
        let outer = push(
            &mut heap,
            &[(Comp, 2), con("f"), (Comp, 2), con("g"), con("a")],
        );
        let same = push(
            &mut heap,
            &[(Comp, 2), con("f"), (Comp, 2), con("g"), con("a")],
        );
        let inner_differs = push(
            &mut heap,
            &[(Comp, 2), con("f"), (Comp, 2), con("g"), con("b")],
        );

        assert!(heap.term_equal(outer, same));
        assert!(!heap.term_equal(outer, inner_differs));
    }

    /// Sets are unordered, so equality has to match elements in any order.
    #[test]
    fn sets_compare_regardless_of_order() {
        let mut heap = heap();
        let a_b = push(&mut heap, &[(Set, 2), con("a"), con("b")]);
        let b_a = push(&mut heap, &[(Set, 2), con("b"), con("a")]);
        let a_c = push(&mut heap, &[(Set, 2), con("a"), con("c")]);

        assert!(heap.term_equal(a_b, b_a));
        assert!(!heap.term_equal(a_b, a_c));
    }

    /// A set holding multi-cell elements: its members have to be found by
    /// walking each one's length, not by assuming a cell apiece.
    #[test]
    fn sets_of_compounds_compare_regardless_of_order() {
        let mut heap = heap();
        let f_a_then_g_b = push(
            &mut heap,
            &[
                (Set, 2),
                (Comp, 2),
                con("f"),
                con("a"),
                (Comp, 2),
                con("g"),
                con("b"),
            ],
        );
        let g_b_then_f_a = push(
            &mut heap,
            &[
                (Set, 2),
                (Comp, 2),
                con("g"),
                con("b"),
                (Comp, 2),
                con("f"),
                con("a"),
            ],
        );
        let differs = push(
            &mut heap,
            &[
                (Set, 2),
                (Comp, 2),
                con("f"),
                con("a"),
                (Comp, 2),
                con("g"),
                con("c"),
            ],
        );

        assert!(heap.term_equal(f_a_then_g_b, g_b_then_f_a));
        assert!(!heap.term_equal(f_a_then_g_b, differs));
    }

    #[test]
    fn sets_of_different_size_differ() {
        let mut heap = heap();
        let two = push(&mut heap, &[(Set, 2), con("a"), con("b")]);
        let one = push(&mut heap, &[(Set, 1), con("a")]);
        assert!(!heap.term_equal(two, one));
    }

    #[test]
    fn lists_compare_element_by_element() {
        let mut heap = heap();
        let a_b = push(&mut heap, &[LIS, con("a"), LIS, con("b"), EMPTY_LIS]);
        let same = push(&mut heap, &[LIS, con("a"), LIS, con("b"), EMPTY_LIS]);
        let reversed = push(&mut heap, &[LIS, con("b"), LIS, con("a"), EMPTY_LIS]);
        let shorter = push(&mut heap, &[LIS, con("a"), EMPTY_LIS]);

        assert!(heap.term_equal(a_b, same));
        assert!(!heap.term_equal(a_b, reversed), "lists are ordered");
        assert!(!heap.term_equal(a_b, shorter));
    }

    #[test]
    fn lists_of_compounds_compare_their_elements() {
        let mut heap = heap();
        let cells = |last: &str| {
            vec![
                LIS,
                (Comp, 2),
                con("f"),
                con("a"),
                LIS,
                con(last),
                EMPTY_LIS,
            ]
        };
        let first = push(&mut heap, &cells("b"));
        let same = push(&mut heap, &cells("b"));
        let differs = push(&mut heap, &cells("c"));

        assert!(heap.term_equal(first, same));
        assert!(!heap.term_equal(first, differs));
    }

    /// Equal text interned twice gets different indices, so strings have to
    /// be compared by content.
    #[test]
    fn strings_compare_by_content() {
        let mut heap = heap();
        let first = push(&mut heap, &[(Stri, SymbolDB::set_string("hi".into()))]);
        let same = push(&mut heap, &[(Stri, SymbolDB::set_string("hi".into()))]);
        let other = push(&mut heap, &[(Stri, SymbolDB::set_string("ho".into()))]);

        assert!(heap.term_equal(first, same));
        assert!(!heap.term_equal(first, other));
    }

    /// Bindings live in the registers, not the cells, so `(Var, i)` and
    /// `(Var, j)` are different cells even when `i` is aliased to `j`. The
    /// walk reports both under the representative, which is the only reason
    /// they compare equal.
    #[test]
    fn variables_aliased_to_one_representative_compare_equal() {
        let mut heap = heap();
        let j = heap.new_var(VarReg::UNBOUND);
        let i = heap.new_var(VarReg::UNBOUND);
        heap.bind(i, VarBind::VarId(j));

        let cell_i = push(&mut heap, &[(Var, i)]);
        let cell_j = push(&mut heap, &[(Var, j)]);

        assert!(heap.term_equal(cell_i, cell_j));
        assert!(heap.term_equal(cell_j, cell_i), "and the other way round");
    }

    #[test]
    fn distinct_unbound_variables_differ() {
        let mut heap = heap();
        let i = heap.new_var(VarReg::UNBOUND);
        let j = heap.new_var(VarReg::UNBOUND);

        let cell_i = push(&mut heap, &[(Var, i)]);
        let cell_j = push(&mut heap, &[(Var, j)]);

        assert!(!heap.term_equal(cell_i, cell_j));
    }

    /// The same aliasing, nested inside a term the walk has to recurse into.
    #[test]
    fn aliased_variables_inside_a_compound_compare_equal() {
        let mut heap = heap();
        let j = heap.new_var(VarReg::UNBOUND);
        let i = heap.new_var(VarReg::UNBOUND);
        let unrelated = heap.new_var(VarReg::UNBOUND);
        heap.bind(i, VarBind::VarId(j));

        let f_i = push(&mut heap, &[(Comp, 2), con("f"), (Var, i)]);
        let f_j = push(&mut heap, &[(Comp, 2), con("f"), (Var, j)]);
        let f_other = push(&mut heap, &[(Comp, 2), con("f"), (Var, unrelated)]);

        assert!(heap.term_equal(f_i, f_j));
        assert!(!heap.term_equal(f_i, f_other));
    }

    #[test]
    fn a_bound_variable_compares_as_the_term_it_names() {
        let mut heap = heap();
        let f_a = push(&mut heap, &[(Comp, 2), con("f"), con("a")]);
        let var_id = heap.set_var(None);
        let var_cell = push(&mut heap, &[(Var, var_id)]);
        heap.bind(var_id, VarBind::Addr(f_a));

        assert!(heap.term_equal(var_cell, f_a));
    }
}
