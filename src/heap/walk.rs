use std::{
    ops::{Deref, DerefMut},
    todo,
};

use smallvec::SmallVec;

use crate::heap::{Cell, Heap, Tag, VarDeref, LIS};

type JumpStack = SmallVec<[(usize, usize); 3]>;
trait JumpStackTrait {
    fn new_stack(addr: usize) -> Self;
    fn next_addr(&mut self) -> Option<usize>;
}
impl JumpStackTrait for JumpStack {
    fn new_stack(addr: usize) -> Self {
        SmallVec::from_buf_and_len([(addr, 1), (0, 0), (0, 0)], 1)
    }

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
}
/// Stack for walking terms and saving indirection points
/// [i].0: current address
/// [i].1: cells left to walk
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
    /// Expects the ref_addr will be consumed
    fn add_jump_frame(&mut self, jump_addr: usize) {
        self.push((jump_addr + 1, 0));
    }

    fn skip_addrs(&mut self, step: usize) {
        unsafe { self.last_mut().unwrap_unchecked().0 += step }
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

    fn next_cell(&mut self, heap: &impl Heap) -> Option<Cell> {
        let addr = self.next_addr()?;
        let cell = match heap.var_deref(addr) {
            VarDeref::Same => heap[addr],
            VarDeref::Jump(jump_addr) => {
                self.push((jump_addr + 1, 0));
                heap[jump_addr]
            }
            VarDeref::Unbound(var_id) => (Tag::Ref, var_id),
        };
        match cell {
            (Tag::Comp | Tag::Tup | Tag::Set, len) => self.increment_cells_left(len),
            LIS => self.increment_cells_left(2),
            _ => (),
        }
        Some(cell)
    }

    fn next_cell_with_addr(&mut self, heap: &impl Heap) -> Option<(usize, Cell)> {
        let addr = self.next_addr()?;
        let (addr, cell) = match heap.var_deref(addr) {
            VarDeref::Same => (addr, heap[addr]),
            VarDeref::Jump(jump_addr) => {
                self.push((jump_addr + 1, 0));
                (jump_addr, heap[jump_addr])
            }
            VarDeref::Unbound(var_id) => (usize::MAX, (Tag::Ref, var_id)),
        };
        match cell {
            (Tag::Comp | Tag::Tup | Tag::Set, len) => self.increment_cells_left(len),
            LIS => self.increment_cells_left(2),
            _ => (),
        }
        Some((addr, cell))
    }
}

impl TermWalk {
    pub fn new(addr: usize) -> TermWalk {
        TermWalk {
            stack: SmallVec::from_buf_and_len([(addr, 1), (0, 0), (0, 0)], 1),
        }
    }

    pub fn sub_walk(&mut self) -> SubWalk {
        let parent_frame = self.last_mut().unwrap();
        let sub_stack = 
            SmallVec::from_buf_and_len([
                (parent_frame.0, parent_frame.1-1),
                (0, 0),
                (0, 0)
            ], 1);
        SubWalk {
            parent_frame,
            sub_stack,
        }
    }
}

impl Walk for TermWalk {}

impl<'a> Walk for SubWalk<'a> {
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
        if self.len() == 1{
            self.parent_frame.1 -= 1;
            self.parent_frame.0 += 1;

        }
        Some(addr)
    }
}

pub struct DualWalk {
    walk1: TermWalk,
    walk2: TermWalk,
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
}
