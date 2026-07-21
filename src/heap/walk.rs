use std::ops::{Deref, DerefMut};

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
    stack: SmallVec<[(usize, usize); 3]>,
}

impl Deref for TermWalk {
    type Target = SmallVec<[(usize, usize); 3]>;

    fn deref(&self) -> &Self::Target {
        &self.stack
    }
}

impl DerefMut for TermWalk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.stack
    }
}

impl TermWalk {
    pub fn new(addr: usize) -> TermWalk {
        TermWalk {
            stack: SmallVec::from_buf_and_len([(addr, 1), (0, 0), (0, 0)], 1),
        }
    }

    pub fn increment_cells_left(&mut self, inc: usize) {
        unsafe { self.stack.last_mut().unwrap_unchecked().1 += inc }
    }

    /// Decrease cells left counter
    /// If cells left would equal zero pop stack and return last ref address
    /// If last frame in stack, pass true in postion 0 of return
    pub fn next_addr(&mut self) -> Option<usize> {
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

    pub fn next_cell(&mut self, heap: &impl Heap) -> Option<Cell> {
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

    /// Add a frame to walk term from de reference
    /// Expects the ref_addr will be consumed
    pub fn add_jump_frame(&mut self, jump_addr: usize) {
        self.stack.push((jump_addr + 1, 0));
    }

    pub fn skip_addrs(&mut self, step: usize) {
        unsafe { self.stack.last_mut().unwrap_unchecked().0 += step }
    }
}
