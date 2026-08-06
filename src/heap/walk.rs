use crate::{heap::VarBind, resolution::Substitution};

use super::{Cell, Heap, Tag::*, VarBind::*, VarReg, LIS};
use smallvec::SmallVec;
use std::ops::{Deref, DerefMut};

type JumpStack = SmallVec<[(usize, usize); 3]>;
/// Stack for walking terms and saving indirection points
/// [i].0: current address
/// [i].1: cells left to walk
#[derive(Debug)]
pub struct TermWalk {
    stack: JumpStack,
}

pub struct SubWalk<'a> {
    parent_frame: &'a mut (usize, usize),
    sub_stack: JumpStack,
}

impl Deref for TermWalk {
    type Target = JumpStack;

    fn deref(&self) -> &Self::Target {
        &self.stack
    }
}

impl DerefMut for TermWalk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.stack
    }
}

impl<'a> Deref for SubWalk<'a> {
    type Target = JumpStack;

    fn deref(&self) -> &Self::Target {
        &self.sub_stack
    }
}

impl<'a> DerefMut for SubWalk<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.sub_stack
    }
}

pub trait Walk: Sized + DerefMut<Target = JumpStack> {
    fn increment_cells_left(&mut self, inc: usize) {
        unsafe { self.last_mut().unwrap_unchecked().1 += inc }
    }

    /// Add a frame to walk term from de reference
    /// Expects the jump_addr will be consumed
    fn add_jump_frame(&mut self, jump_addr: usize) {
        self.push((jump_addr + 1, 0));
    }

    fn skip_addrs(&mut self, step: usize) {
        unsafe {
            let top_frame = self.last_mut().unwrap_unchecked();
            top_frame.0 += step;
            top_frame.1 -= step;
        }
    }

    /// Decrease cells left counter
    /// If cells left would equal zero pop stack and return last ref address
    /// If last frame in stack, pass true in postion 0 of return
    fn next_addr(&mut self) -> Option<usize> {
        let mut frame = self.last_mut()?;
        loop {
            if frame.1 == 0 {
                self.pop();
                frame = self.last_mut()?;
            } else {
                break;
            }
        }
        let addr = frame.0;
        frame.1 -= 1;
        frame.0 += 1;
        Some(addr)
    }

    fn handle_var_bind(
        &mut self,
        var_bind: VarBind,
        heap: &impl Heap,
        addr: &mut usize,
        cell: &mut Cell,
    ) {
        match var_bind {
            Var(var_id) => *cell = (Ref, var_id),
            Addr(jump_addr) => {
                self.add_jump_frame(jump_addr);
                (*addr, *cell) = (jump_addr, heap[jump_addr])
            }
        }
    }

    fn handle_ref(&mut self, heap: &impl Heap, addr: &mut usize, cell: &mut Cell) {
        if let (Ref, var_id) = cell {
            match heap.var_deref(*var_id) {
                Var(var_id) => cell.1 = var_id,
                Addr(jump_addr) => {
                    self.add_jump_frame(jump_addr);
                    (*addr, *cell) = (jump_addr, heap[jump_addr])
                }
            }
        }
    }

    fn handle_cell_increment(&mut self, cell: Cell) {
        match cell {
            (Comp | Tup | Set, len) => self.increment_cells_left(len),
            LIS => self.increment_cells_left(2),
            _ => (),
        }
    }

    fn next_cell(&mut self, heap: &impl Heap) -> Option<Cell> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];
        self.handle_ref(heap, &mut addr, &mut cell);
        self.handle_cell_increment(cell);
        Some(cell)
    }

    fn next_cell_with_addr(&mut self, heap: &impl Heap) -> Option<(usize, Cell)> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];
        self.handle_ref(heap, &mut addr, &mut cell);
        self.handle_cell_increment(cell);
        Some((addr, cell))
    }

    fn next_cell_with_addr_arg_deref(
        &mut self,
        heap: &impl Heap,
        sub: &Substitution,
    ) -> Option<(usize, Cell)> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];
        match cell {
            (Arg, arg_id) if let Some(var_bind) = sub.get_arg(arg_id) => {
                self.handle_var_bind(var_bind, heap, &mut addr, &mut cell)
            }
            (Ref, var_id) => {
                self.handle_var_bind(heap.var_deref(var_id), heap, &mut addr, &mut cell);
            }
            _ => (),
        }
        self.handle_cell_increment(cell);
        Some((addr, cell))
    }

    fn print_jump_stack(&self) {
        println!("|---------|");
        println!("|Addr|N2Go|");
        println!("|---------|");
        for (addr, n2go) in self.iter() {
            println!("|{addr:4}|{n2go:4}|");
            println!("|---------|");
        }
    }
}

impl TermWalk {
    pub fn new(addr: usize) -> TermWalk {
        TermWalk {
            stack: SmallVec::from_buf_and_len([(addr, 1), (0, 0), (0, 0)], 1),
        }
    }

    //Create Sub walk from last provided address
    pub fn sub_walk<'a>(&'a mut self, heap: &impl Heap) -> SubWalk<'a> {
        // take top frame, undo last handle cell increment
        let parent_frame = self.last_mut().unwrap();
        let last_addr = parent_frame.0 - 1;
        match heap[last_addr] {
            (Comp | Tup | Set, len) => parent_frame.1 -= len,
            LIS => parent_frame.1 -= 2,
            _ => (),
        }

        let sub_stack = SmallVec::from_buf_and_len([(last_addr, 1), (0, 0), (0, 0)], 1);
        SubWalk {
            parent_frame,
            sub_stack,
        }
    }
}

impl Walk for TermWalk {}

impl<'a> Walk for SubWalk<'a> {
    fn next_addr(&mut self) -> Option<usize> {
        let mut frame = self.last_mut()?;
        loop {
            if frame.1 == 0 {
                let addr = frame.0;
                self.pop();
                match self.last_mut() {
                    Some(next_frame) => frame = next_frame,
                    None => {
                        self.parent_frame.0 = addr;
                        return None;
                    }
                }
            } else {
                break;
            }
        }
        let addr = frame.0;
        frame.1 -= 1;
        frame.0 += 1;
        Some(addr)
    }
}

pub struct DualWalk {
    pub(crate) walk1: TermWalk,
    pub(crate) walk2: TermWalk,
}

impl DualWalk {
    pub fn new(addr1: usize, addr2: usize) -> Self {
        Self {
            walk1: TermWalk::new(addr1),
            walk2: TermWalk::new(addr2),
        }
    }

    pub fn next_cells(&mut self, heap: &impl Heap) -> Option<(Cell, Cell)> {
        Some((self.walk1.next_cell(heap)?, self.walk2.next_cell(heap)?))
    }

    pub fn next_cells_with_addrs(
        &mut self,
        heap: &impl Heap,
    ) -> Option<((usize, Cell), (usize, Cell))> {
        Some((
            self.walk1.next_cell_with_addr(heap)?,
            self.walk2.next_cell_with_addr(heap)?,
        ))
    }

    pub fn next_cells_with_addrs_arg_deref(
        &mut self,
        heap: &impl Heap,
        sub: &Substitution,
    ) -> Option<((usize, Cell), (usize, Cell))> {
        Some((
            self.walk1.next_cell_with_addr_arg_deref(heap, sub)?,
            self.walk2.next_cell_with_addr_arg_deref(heap, sub)?,
        ))
    }
}

#[cfg(test)]
#[allow(dead_code)]
#[allow(unused)]
mod test {
    use core::panic;
    use std::{assert_eq, vec};

    use crate::{
        heap::{QueryHeap, SymbolDB, EMPTY_LIS},
        resolution::Substitution,
    };

    use super::*;

    #[test]
    fn next_addr() {
        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(0, 0)]),
        };
        assert_eq!(walk.next_addr(), None);

        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(0, 1)]),
        };
        assert_eq!(walk.next_addr(), Some(0));
        assert_eq!(walk.next_addr(), None);

        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(10, 0), (20, 0), (30, 1), (40, 0)]),
        };
        assert_eq!(walk.next_addr(), Some(30));
        assert_eq!(walk.next_addr(), None);
    }

    #[test]
    fn handle_cell_increment() {
        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(0, 0)]),
        };
        walk.handle_cell_increment(LIS);
        assert_eq!(walk[0], (0, 2));

        walk.handle_cell_increment((Comp, 2));
        assert_eq!(walk[0], (0, 4));

        walk.handle_cell_increment((Tup, 2));
        assert_eq!(walk[0], (0, 6));

        walk.handle_cell_increment((Set, 2));
        assert_eq!(walk[0], (0, 8));
    }

    #[test]
    fn handle_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);

        // Handle ref bound to ref
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(2, 1)]),
        };
        let mut addr = 1;
        let mut cell = (Ref, 0);
        walk.handle_ref(&heap, &mut addr, &mut cell);
        assert_eq!(walk.as_slice(), &[(2, 1)]);
        assert_eq!(cell, (Ref, 1));

        // Handle jump to con
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1), (Con, a)];
        heap.var_regs = vec![Var(1).into(), Addr(3).into()];
        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(2, 1)]),
        };
        let mut addr = 1;
        let mut cell = (Ref, 0);
        walk.handle_ref(&heap, &mut addr, &mut cell);
        assert_eq!(walk.as_slice(), &[(2, 1), (4, 0)]);
        assert_eq!(cell, (Con, a));
        assert_eq!(addr, 3);

        // Handle jump to strucuture
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), Addr(0).into()];
        let mut walk = TermWalk {
            stack: JumpStack::from_vec(vec![(5, 1)]),
        };
        let mut addr = 4;
        let mut cell = (Ref, 0);
        walk.handle_ref(&heap, &mut addr, &mut cell);
        assert_eq!(walk.as_slice(), &[(5, 1), (1, 0)]);
        assert_eq!(cell, (Comp, 2));
    }

    #[test]
    fn next_cell() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);

        // Handle ref bound to ref
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Ref, 1)));
        assert_eq!(walk.next_cell(&heap), Some((Ref, 1)));
        assert_eq!(walk.next_cell(&heap), None);

        // Handle jump to con
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1), (Con, a)];
        heap.var_regs = vec![Var(1).into(), Addr(3).into()];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), None);

        // Handle jump to strucuture
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), Addr(0).into()];
        let mut walk = TermWalk::new(3);
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), None);

        // Handle jump to strucuture
        heap.cells = vec![
            (Comp, 2),
            (Ref, 0),
            (Con, a),
            (Comp, 2),
            (Con, p),
            (Ref, 1),
            LIS,
            (Con, p),
            LIS,
            (Con, a),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(3).into(), Addr(6).into()];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some(LIS));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some(LIS));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), Some(EMPTY_LIS));
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert_eq!(walk.next_cell(&heap), None);
    }

    #[test]
    fn next_cell_with_addr() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);

        // Handle ref bound to ref
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell_with_addr(&heap), Some((0, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((1, (Ref, 1))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((2, (Ref, 1))));
        assert_eq!(walk.next_cell_with_addr(&heap), None);

        // Handle jump to con
        heap.cells = vec![(Comp, 2), (Ref, 0), (Ref, 1), (Con, a)];
        heap.var_regs = vec![Var(1).into(), Addr(3).into()];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell_with_addr(&heap), Some((0, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((3, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((3, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), None);

        // Handle jump to strucuture
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![Var(1).into(), Addr(0).into()];
        let mut walk = TermWalk::new(3);
        assert_eq!(walk.next_cell_with_addr(&heap), Some((3, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((0, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((1, (Con, p))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((2, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((0, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((1, (Con, p))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((2, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), None);

        // Handle jump to strucuture
        heap.cells = vec![
            (Comp, 2),
            (Ref, 0),
            (Con, a),
            (Comp, 2),
            (Con, p),
            (Ref, 1),
            LIS,
            (Con, p),
            LIS,
            (Con, a),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(3).into(), Addr(6).into()];
        let mut walk = TermWalk::new(0);
        assert_eq!(walk.next_cell_with_addr(&heap), Some((0, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((3, (Comp, 2))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((4, (Con, p))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((6, LIS)));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((7, (Con, p))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((8, (LIS))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((9, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((10, EMPTY_LIS)));
        assert_eq!(walk.next_cell_with_addr(&heap), Some((2, (Con, a))));
        assert_eq!(walk.next_cell_with_addr(&heap), None);
    }

    fn accumulate_cells(
        heap: &QueryHeap,
        walk: &mut impl Walk,
        subs: &Substitution,
    ) -> Vec<(usize, Cell)> {
        let mut cells = Vec::new();
        while let Some(cell) = walk.next_cell_with_addr_arg_deref(heap, subs) {
            cells.push(cell);
            if cells.len() > 15 {
                for cell in cells {
                    println!("{cell:?}");
                }
                walk.print_jump_stack();
                panic!()
            }
        }
        cells
    }

    #[test]
    fn next_cell_with_addr_arg_deref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        let mut subs = Substitution::default();

        // Handle arg jump to strucuture
        heap.cells = vec![(Comp, 2), (Arg, 0), (Arg, 1), (Comp, 2), (Con, p), (Con, a)];
        subs.set_arg(0, Addr(3));
        subs.set_arg(1, Addr(3));
        let mut walk = TermWalk::new(0);
        let cells = accumulate_cells(&heap, &mut walk, &subs);
        assert_eq!(cells.len(), 7);
        assert_eq!(cells[0], (0, (Comp, 2)));
        assert_eq!(cells[1], (3, (Comp, 2)));
        assert_eq!(cells[2], (4, (Con, p)));
        assert_eq!(cells[3], (5, (Con, a)));
        assert_eq!(cells[4], (3, (Comp, 2)));
        assert_eq!(cells[5], (4, (Con, p)));
        assert_eq!(cells[6], (5, (Con, a)));

        // Arg -> Ref -> strucutre
        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0), (Comp, 2), (Con, p), (Con, a)];
        let mut sub = Substitution::default();
        sub.set_arg(0, Var(0));
        heap.var_regs = vec![Addr(3).into()];
        let mut walk = TermWalk::new(0);
        let cells = accumulate_cells(&heap, &mut walk, &sub);
        assert_eq!(cells.len(), 5);
        assert_eq!(cells[0], (0, (Comp, 2)));
        assert_eq!(cells[1], (1, (Con, p)));
        assert_eq!(cells[2], (3, (Comp, 2)));
        assert_eq!(cells[3], (4, (Con, p)));
        assert_eq!(cells[4], (5, (Con, a)));

        // Arg -> Ref -> Ref -> strucutre

        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0), (Comp, 2), (Con, p), (Con, a)];
        heap.var_regs = vec![Var(1).into(), Addr(3).into()];
        let mut walk = TermWalk::new(0);
        let cells = accumulate_cells(&heap, &mut walk, &sub);
        assert_eq!(cells.len(), 5);
        assert_eq!(cells[0], (0, (Comp, 2)));
        assert_eq!(cells[1], (1, (Con, p)));
        assert_eq!(cells[2], (3, (Comp, 2)));
        assert_eq!(cells[3], (4, (Con, p)));
        assert_eq!(cells[4], (5, (Con, a)));
    }

    #[test]
    fn sub_walk_simple() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        let subs = Substitution::default();

        //p(X(X,X),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            (Con, a),
        ];
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [(2, (Comp, 3)), (3, (Arg, 0)), (4, (Arg, 0)), (5, (Arg, 0)),]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());
    }

    #[test]
    fn sub_walk_with_ref_jump() {
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        let subs = Substitution::default();

        //p(q((a,a)),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Ref, 0),
            (Con, a),
            (Tup, 2),
            (Con, a),
            (Con, a),
        ];
        heap.var_regs.push(Addr(6).into());
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [
                (2, (Comp, 2)),
                (3, (Con, q)),
                (6, (Tup, 2)),
                (7, (Con, a)),
                (8, (Con, a)),
            ]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());
    }

    #[test]
    fn sub_walk_with_arg_jump() {
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        let mut subs = Substitution::default();

        //p(q((a,a)),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Arg, 0),
            (Con, a),
            (Tup, 2),
            (Con, a),
            (Con, a),
        ];
        subs.set_arg(0, Addr(6));
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [
                (2, (Comp, 2)),
                (3, (Con, q)),
                (6, (Tup, 2)),
                (7, (Con, a)),
                (8, (Con, a)),
            ]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());
    }

    #[test]
    fn sub_walk_with_arg_ref_jump() {
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let mut heap = QueryHeap::new(&[], None);
        let mut subs = Substitution::default();

        //Arg jump first
        //p(q(((b,b),a)),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Arg, 0),
            (Con, a),
            (Tup, 2),
            (Ref, 0),
            (Con, a),
            (Tup, 2),
            (Con, b),
            (Con, b),
        ];
        subs.set_arg(0, Addr(6));
        heap.var_regs.push(Addr(9).into());
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [
                (2, (Comp, 2)),
                (3, (Con, q)),
                (6, (Tup, 2)),
                (9, (Tup, 2)),
                (10, (Con, b)),
                (11, (Con, b)),
                (8, (Con, a)),
            ]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());

        //Ref jump first
        //p(q(((b,b),a)),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Ref, 0),
            (Con, a),
            (Tup, 2),
            (Arg, 0),
            (Con, a),
            (Tup, 2),
            (Con, b),
            (Con, b),
        ];
        let mut subs = Substitution::default();
        subs.set_arg(0, Addr(9));
        heap.var_regs[0] = Addr(6).into();
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [
                (2, (Comp, 2)),
                (3, (Con, q)),
                (6, (Tup, 2)),
                (9, (Tup, 2)),
                (10, (Con, b)),
                (11, (Con, b)),
                (8, (Con, a)),
            ]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());

        //arg -> ref -> addr
        //p(q((a,a)),a)
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Arg, 0),
            (Con, a),
            (Tup, 2),
            (Con, a),
            (Con, a),
        ];
        let mut subs = Substitution::default();
        subs.set_arg(0, Var(0));
        heap.var_regs = vec![Var(1).into(), Addr(6).into()];
        let mut walk = TermWalk::new(0);
        //walk to first argument
        assert_eq!(walk.next_cell(&heap), Some((Comp, 3)));
        assert_eq!(walk.next_cell(&heap), Some((Con, p)));
        assert_eq!(walk.next_cell(&heap), Some((Comp, 2)));
        //create sub_walk
        let mut sub_walk = walk.sub_walk(&heap);
        let cells = accumulate_cells(&heap, &mut sub_walk, &subs);
        assert_eq!(
            cells,
            [
                (2, (Comp, 2)),
                (3, (Con, q)),
                (6, (Tup, 2)),
                (7, (Con, a)),
                (8, (Con, a)),
            ]
        );
        assert_eq!(walk.next_cell(&heap), Some((Con, a)));
        assert!(walk.next_cell(&heap).is_none());
    }

    #[test]
    fn return_from_jump_before_subwalk() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let heap = QueryHeap::new(&[], None);
        let subs = Substitution::default();
    }
}
