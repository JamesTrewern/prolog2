use std::{
    cell,
    ops::{Deref, DerefMut},
    println, todo,
};

use smallvec::SmallVec;

use super::{
    Cell, Heap,
    Tag::*,
    VarBind::*,
    VarReg, LIS,
};

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

    fn handle_ref(&mut self, heap: &impl Heap, addr: &mut usize, cell: &mut Cell) {
        if let (Ref, var_id) = cell {
            match heap.var_deref(*var_id) {
                Var(var_id) => cell.1 = var_id,
                Addr(jump_addr) => {
                    self.push((jump_addr + 1, 0));
                    (*addr, *cell) = (jump_addr, heap[jump_addr])
                }
            }
        }
    }

    fn next_cell(&mut self, heap: &impl Heap) -> Option<Cell> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];
        self.handle_ref(heap, &mut addr, &mut cell);

        match cell {
            (Comp | Tup | Set, len) => self.increment_cells_left(len),
            LIS => self.increment_cells_left(2),
            _ => (),
        }
        Some(cell)
    }

    fn next_cell_with_addr(&mut self, heap: &impl Heap) -> Option<(usize, Cell)> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];
        self.handle_ref(heap, &mut addr, &mut cell);
        match cell {
            (Comp | Tup | Set, len) => self.increment_cells_left(len),
            LIS => self.increment_cells_left(2),
            _ => (),
        }
        Some((addr, cell))
    }

    fn next_cell_with_addr_arg_deref(
        &mut self,
        heap: &impl Heap,
        arg_regs: &[VarReg],
    ) -> Option<(usize, Cell)> {
        let mut addr = self.next_addr()?;
        let mut cell = heap[addr];

        if let (Arg, arg_id) = cell {
            let arg = arg_regs[arg_id];
            if arg.bound() {
                if arg.addr() {
                    let jump_addr = arg.0;
                    self.push((jump_addr + 1, 0));
                    (addr, cell) = (jump_addr, heap[jump_addr])
                } else {
                    cell = (Ref, arg.value())
                }
            }
        }

        self.handle_ref(heap, &mut addr, &mut cell);

        match cell {
            (Comp | Tup | Set, len) => self.increment_cells_left(len),
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
        println!("{self:?}");
        let parent_frame = self.last_mut().unwrap();
        let sub_stack =
            SmallVec::from_buf_and_len([(parent_frame.0, parent_frame.1 - 1), (0, 0), (0, 0)], 1);
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
        if self.len() == 1 {
            self.parent_frame.1 -= 1;
            self.parent_frame.0 += 1;
        }
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
        arg_regs: &[VarReg]
    ) -> Option<((usize, Cell), (usize, Cell))> {
        Some((
            self.walk1.next_cell_with_addr_arg_deref(heap,arg_regs)?,
            self.walk2.next_cell_with_addr_arg_deref(heap,arg_regs)?,
        ))
    }
}
