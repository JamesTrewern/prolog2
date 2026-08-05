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
    ops::{Index, IndexMut, Range, RangeInclusive},
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
pub const _FALSE: Cell = (Con, CON_PTR);
pub const _TRUE: Cell = (Con, CON_PTR + 1);
pub const LIS: Cell = (Lis, 0);
pub const EMPTY_LIS: Cell = (ELis, 0);

/// Core trait for heap storage.
///
/// Implemented by both the static program heap (`Vec<Cell>`) and the
/// query-time [`super::query_heap::QueryHeap`]. Provides cell access,
/// term construction, dereferencing, and display.
pub trait Heap:
    Sized + IndexMut<usize, Output = Cell> + Index<Range<usize>, Output = [Cell]>
{
    /// Reset Ref cells affected by binding to self references
    /// @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    fn unbind(&mut self, binding: &[usize]);

    /// Update address value of ref cells affected by binding
    /// @binding: List of (usize, usize) tuples representing heap indexes, left -> right
    fn bind(&mut self, var_id: usize, binding: VarBind);

    fn heap_push(&mut self, cell: Cell) -> usize;

    fn heap_len(&self) -> usize;

    fn truncate(&mut self, len: usize);

    fn heap_last(&mut self) -> &mut Cell;

    fn set_var(&mut self, var_id: Option<usize>) -> usize;

    fn bound(&self, var_id: usize) -> Option<VarBind>;

    /// Return VarBind for a given var_id
    /// If var_id unbound return Unbound
    /// If var_id bound follow binding chains
    /// Return either last unbound var as Var(var_id)
    /// Or return Addr(addr)
    fn var_deref(&self, var_id: usize) -> VarBind;

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
            if (!args && tag == Ref) | (args && tag == Arg) {
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
                (Arg, arg_id) => {
                    if let Some(pos) = args.iter().position(|&arg_id2| arg_id == arg_id2) {
                        println!("pos: {pos}, arg_id: {arg_id}");
                        self[addr].1 = pos;
                    } else {
                        self[addr].1 = args.len();
                        args.push(arg_id);
                    }
                }
                LIS => cells_left += 2,
                (Comp | Set | Tup, len) => cells_left += len,
                _ => (),
            }
            addr += 1;
        }
    }

    fn occurs(&self, addr: usize, var_id: usize, bound_args: &[usize]) -> bool {
        let mut walk = TermWalk::new(addr);
        while let Some(cell) = walk.next_cell(self) {
            match cell {
                (Arg, id) if bound_args.contains(&id) => {
                    return true;
                }
                (Ref, var_id2) if var_id2 == var_id => {
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
            if functor.0 == Ref {
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

    /// Given address to a str cell create an operator over the sub terms addresses, including functor/predicate
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
            if tag == Ref {
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
            if tag == Ref {
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

    fn term_equal(&self, addr1: usize, addr2: usize) -> bool {
        println!("{} =:= {}", self.term_string(addr1), self.term_string(addr2));
        let (mut walk1, mut walk2) = (TermWalk::new(addr1), TermWalk::new(addr2));
        loop {
            let (Some(cell1), Some(cell2)) = (walk1.next_cell(self), walk2.next_cell(self)) else {
                return true;
            };

            match (cell1, cell2) {
                ((Set, len1), (Set, len2)) if len1 == len2 => {
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
                ((Stri, i1), (Stri, i2)) => {
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

    ///Debug function for printing formatted string of current heap state
    fn _print_heap(&self) {
        let w = 6;
        for i in 0..self.heap_len() {
            let (tag, value) = self[i];
            match tag {
                Con => {
                    println!("[{i:3}]|{tag:w$}|{:w$}|", SymbolDB::get_const(value))
                }
                Lis => println!("[{i:3}]|{tag:w$}|{value:w$}|"),
                ELis => println!("[{i:3}]|{tag:w$}|{:w$}|", "[]"),
                Ref | Arg => {
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
            Ref => match self.var_deref(self[*addr].1) {
                Addr(mut ref_addr) => self.term_string_rec(&mut ref_addr, buf),
                Var(var_id) => match SymbolDB::get_var(var_id, self.get_id(*addr)).to_owned() {
                    Some(symbol) => buf.write_str(&symbol),
                    None => write!(buf, "Ref_{}", self[*addr].1),
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
        self.resize(len, (Ref, 0));
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
        VarBind::{Addr, Var},
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
            Var(1).into(),
            Var(2).into(),
            Addr(3).into(),
            Var(4).into(),
            Var(5).into(),
            VarReg::UNBOUND,
        ]);

        assert_eq!(Addr(3), heap.var_deref(0));
        assert_eq!(Addr(3), heap.var_deref(1));
        assert_eq!(Addr(3), heap.var_deref(2));
        assert_eq!(Var(5), heap.var_deref(3));
        assert_eq!(Var(5), heap.var_deref(4));
        assert_eq!(Var(5), heap.var_deref(5));
    }

    #[test]
    fn dereference() {
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        heap.var_regs.extend_from_slice(&[
            Var(1).into(),
            Var(2).into(),
            Addr(3).into(),
            VarReg::UNBOUND,
        ]);

        heap.cells = vec![(Ref, 0), (Ref, 1), (Ref, 2), (Ref, 3)];
        assert_eq!(heap.term_string(0), "Ref_3");

        heap.cells = vec![(Ref, 0), (Ref, 1), (Ref, 2), (Arg, 0)];
        assert_eq!(heap.term_string(0), "Arg_0");

        heap.cells = vec![(Ref, 0), (Ref, 1), (Ref, 2), (Con, a)];
        assert_eq!(heap.term_string(0), "a");

        heap.cells = vec![
            (Ref, 0),
            (Ref, 1),
            (Ref, 2),
            (Comp, 3),
            (Con, f),
            (Con, a),
            (Ref, 3),
        ];
        assert_eq!(heap.term_string(0), "f(a,Ref_3)");

        heap.cells = vec![(Ref, 0), (Ref, 1), (Ref, 2), (Tup, 2), (Con, a), (Ref, 3)];
        assert_eq!(heap.term_string(0), "(a,Ref_3)");

        heap.cells = vec![(Ref, 0), (Ref, 1), (Ref, 2), (Set, 2), (Con, a), (Ref, 3)];
        assert_eq!(heap.term_string(0), "{a,Ref_3}");

        heap.cells = vec![
            (Ref, 0),
            (Ref, 1),
            (Ref, 2),
            LIS,
            (Con, a),
            LIS,
            (Ref, 3),
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
        other.cells = vec![(Tup, 4), (Ref, 0), (Ref, 1), (Ref, 2), (Ref, 3)];
        other.var_regs = vec![
            Var(1).into(),
            Var(2).into(),
            VarReg::UNBOUND,
            VarReg::UNBOUND,
        ];
        heap.clone_term_from_other(&other, 0, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Tup, 4), (Ref, 0), (Ref, 0), (Ref, 0), (Ref, 1),]
        );

        // Ref bound to simple term
        heap.cells.clear();
        heap.var_regs.clear();
        //(a,a)
        other.cells = vec![
            (Con, a),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
            (Tup, 2),
            (Ref, 2),
            (Ref, 3),
        ];
        other.var_regs = vec![Var(1).into(), Addr(0).into(), Var(3).into(), Addr(0).into()];
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
            (Ref, 0),  // 5
            (Comp, 2), // 6
            (Con, p),  // 7
            (Ref, 1),  // 8
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
            (Ref, 0),  // 5
            (Comp, 2), // 6
            (Con, p),  // 7
            (Ref, 1),  // 8
        ];
        other.var_regs = vec![Addr(0).into(), Addr(3).into()];
        heap.clone_term_from_other(&other, 6, &mut HashMap::new());
        assert_eq!(
            &heap.cells,
            &[(Comp, 2), (Con, p), LIS, (Con, p), LIS, (Con, f), (Con, a),]
        );
    }

    #[test]
    fn normalise_args() {
        let mut norm_args_map = Vec::new();
        let mut heap = vec![
            (Comp, 3),
            (Arg, 2),
            (Arg, 4),
            (Arg, 1),
            (Comp, 1),
            LIS,
            (Arg, 1),
            LIS,
            (Arg, 4),
            LIS,
            (Arg, 2),
            EMPTY_LIS,
        ];
        heap.normalise_args(0, &mut norm_args_map);
        heap.normalise_args(4, &mut norm_args_map);

        assert_eq!(
            &heap,
            &[
                (Comp, 3),
                (Arg, 0),
                (Arg, 1),
                (Arg, 2),
                (Comp, 1),
                LIS,
                (Arg, 2),
                LIS,
                (Arg, 1),
                LIS,
                (Arg, 0),
                EMPTY_LIS
            ]
        )
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
        heap.cells = vec![(Con, p), (Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), Addr(0).into()];
        assert_eq!(heap.symbol_arity(1), (p, 1));

        //Unbound var + chain to unbound var
        heap.cells = vec![(Comp, 2), (Ref, 0), (Con, a), (Comp, 2), (Ref, 1), (Ref, 2)];
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        assert_eq!(heap.symbol_arity(0), (0, 1));
        assert_eq!(heap.symbol_arity(3), (0, 1));
    }
}
