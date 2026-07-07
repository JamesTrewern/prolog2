use smallvec::SmallVec;

type DerefStack = SmallVec<[(usize, usize); 3]>;
/// Stack for walking terms and saving indirection points
/// [i].0: current address
/// [i].1: cells left to walk
#[derive(Debug)]
pub struct TermWalk {
    stack: DerefStack,
    pointer: usize,
}

impl TermWalk {
    pub fn new(addr: usize) -> TermWalk {
        let mut stack = SmallVec::new();
        stack.push((addr, 1));
        TermWalk { stack, pointer: 0 }
    }

    pub fn increment_cells_left(&mut self, inc: usize) {
        self.stack[self.pointer].1 += inc;
    }

    /// Decrease cells left counter
    /// If cells left would equal zero pop stack and return last ref address
    /// If last frame in stack, pass true in postion 0 of return
    pub fn next_addr(&mut self) -> Option<usize> {
        next_addr(&mut self.stack, &mut self.pointer)
    }

    /// Add a frame to walk term from de reference
    /// Expects the ref_addr will be consumed
    pub fn add_deref_frame(&mut self, ref_addr: usize) {
        self.stack.push((ref_addr + 1, 0));
        self.pointer += 1;
    }

    pub fn skip_addrs(&mut self, step: usize) {
        self.stack[self.pointer].0 += step
    }
}

pub struct DualWalk {
    stack1: DerefStack,
    p1: usize,
    stack2: DerefStack,
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
        match (
            next_addr(&mut self.stack1, &mut self.p1),
            next_addr(&mut self.stack2, &mut self.p2),
        ) {
            (Some(addr1), Some(addr2)) => Some((addr1, addr2)),
            (None, None) => None,
            _ => unreachable!("Walk stacks can't have different cells left count"),
        }
    }

    /// Add a frame to walk term from de reference
    /// Expects the ref_addr will be consumed
    pub fn add_deref_frame(&mut self, ref_addr: usize, first: bool) {
        if first {
            self.stack1.push((ref_addr + 1, 0));
            self.p1 += 1;
        } else {
            self.stack2.push((ref_addr + 1, 0));
            self.p2 += 1;
        }
    }

    pub fn skip_addrs(&mut self, step: usize) {
        unsafe {
            self.stack1.last_mut().unwrap_unchecked().0 += step;
            self.stack2.last_mut().unwrap_unchecked().0 += step;
        };
    }
}

fn next_addr(stack: &mut DerefStack, pointer: &mut usize) -> Option<usize> {
    let mut frame = &mut stack[*pointer];
    loop {
        if frame.1 == 0 {
            if *pointer == 0 {
                return None;
            }
            stack.pop();
            *pointer -= 1;
            frame = &mut stack[*pointer];
        } else {
            break;
        }
    }
    let addr = frame.0;
    frame.1 -= 1;
    frame.0 += 1;
    Some(addr)
}
