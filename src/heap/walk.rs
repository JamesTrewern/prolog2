use smallvec::SmallVec;

/// Stack for walking terms and saving indirection points
/// [i].0: current address
/// [i].1: cells left to walk
pub struct TermWalk {
    stack: SmallVec<[(usize, usize); 3]>,
    pointer: usize,
}

impl TermWalk {
    pub fn new(addr: usize) -> TermWalk {
        let mut stack = SmallVec::new();
        stack.push((addr, 1));
        TermWalk { stack, pointer: 0 }
    }

    pub fn increment_cells_left(&mut self, inc: usize) {
        self.stack[self.pointer].1 += 1;
    }

    /// Decrease cells left counter
    /// If cells left would equal zero pop stack and return last ref address
    /// If last frame in stack, pass true in postion 0 of return
    pub fn next_addr(&mut self) -> Option<usize> {
        let mut frame = self.stack[self.pointer];
        loop {
            if frame.1 == 0 {
                if self.pointer == 0 {
                    return None;
                }
                self.stack.pop();
                self.pointer -= 1;
                frame = self.stack[self.pointer];
            } else {
                break;
            }
        }
        let addr = frame.0;
        frame.1 -= 1;
        frame.0 += 1;
        Some(addr)
    }

    /// Add a frame to walk term from de reference
    /// Expects the ref_addr will be consumed
    pub fn add_frame(&mut self, ref_addr: usize) {
        self.stack.push((ref_addr + 1, 0));
    }

    pub fn skip_addrs(&mut self, step: usize) {
        self.stack[self.pointer].0 += step
    }
}

pub struct DualWalk {
    stack1: SmallVec<[(usize, usize); 3]>,
    p1: usize,
    stack2: SmallVec<[(usize, usize); 3]>,
    p2: usize,
}

impl DualWalk {
    pub fn new(addr1: usize, addr2: usize) -> DualWalk {
        let mut stack1 = SmallVec::new();
        let mut stack2 = SmallVec::new();
        stack1.push((addr1, 1));
        stack2.push((addr2, 1));
        DualWalk {
            stack1,
            p1: 0,
            stack2,
            p2: 0,
        }
    }

    pub fn increment_cells_left(&mut self, inc: usize) {
        self.stack1[self.p1].1 += inc;
        self.stack2[self.p2].1 += inc;
    }

    /// Decrease cells left counter
    /// If cells left would equal zero pop stack and return last ref address
    /// If last frame in stack, pass true in postion 0 of return
    pub fn next_addrs(&mut self) -> Option<(usize, usize)> {
        let mut frame = self.stack1[self.p1];
        loop {
            if frame.1 == 0 {
                if self.p1 == 0 {
                    return None;
                }
                self.stack1.pop();
                self.p1 -= 1;
                frame = self.stack1[self.p1];
            } else {
                break;
            }
        }
        let addr1 = frame.0;
        frame.1 -= 1;
        frame.0 += 1;

        frame = self.stack2[self.p2];
        loop {
            if frame.1 == 0 {
                if self.p2 == 0 {
                    unreachable!("Stacks should not have different cells left")
                }
                self.stack2.pop();
                self.p2 -= 1;
                frame = self.stack2[self.p2];
            } else {
                break;
            }
        }
        let addr2 = frame.0;
        frame.1 -= 1;
        frame.0 += 1;

        Some((addr1, addr2))
    }

    /// Add a frame to walk term from de reference
    /// Expects the ref_addr will be consumed
    pub fn add_frame(&mut self, ref_addr: usize, first: bool) {
        if first {
            self.stack1.push((ref_addr + 1, 0));
        } else {
            self.stack2.push((ref_addr + 1, 0));
        }
    }

    pub fn skip_addrs(&mut self, step: usize) {
        unsafe {
            self.stack1.last_mut().unwrap_unchecked().0 += step;
            self.stack2.last_mut().unwrap_unchecked().0 += step;
        };
    }
}
