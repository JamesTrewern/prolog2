use crate::heap::{self, Heap};

pub type Clause = Box<[usize]>;

pub trait ClauseTraits {
    fn pred_symbol(&self, heap: &Heap) -> usize;
    fn higher_order(&self, heap: &Heap) -> bool;
    fn write_clause(&self, heap: &Heap);
}

impl ClauseTraits for Clause {
    fn higher_order(&self, heap: &Heap) -> bool {
        self.iter().any(|literal| ho_term(*literal, heap))
    }

    fn write_clause(&self, heap: &Heap) {
        if self.len() == 1 {
            let clause_str = heap.term_string(self[0]);
            println!("{clause_str}.")
        } else {
            let mut buffer: String = String::new();
            buffer += &heap.term_string(self[0]);
            buffer += ":-";
            let mut i = 1;
            loop {
                buffer += &heap.term_string(self[i]);
                i += 1;
                if i == self.len() {
                    break;
                } else {
                    buffer += ","
                }
            }
            println!("{buffer}.");
        }
    }

    fn pred_symbol(&self, heap: &Heap) -> usize{
        heap[self[0]].0
    }
}

fn ho_struct(addr: usize, heap: &Heap) -> bool {
    let (p, n) = heap[addr];
    if p < isize::MAX as usize {
        return true;
    }
    for i in 1..n + 1 {
        match heap[addr + i] {
            (Heap::REFA, _) => return true,
            (Heap::STR, ptr) => {
                if ho_struct(ptr, heap) {
                    return true;
                }
            }
            _ => (),
        }
    }
    false
}

fn ho_list(addr: usize, heap: &Heap) -> bool {
    if ho_term(addr, heap) {
        return true;
    }
    if ho_term(addr + 1, heap) {
        return true;
    }
    false
}

fn ho_term(addr: usize, heap: &Heap) -> bool {
    match heap[addr] {
        (Heap::REFA, _) => return true,
        (Heap::STR, ptr) => {
            if ho_struct(ptr, heap) {
                return true;
            }
        }
        (Heap::LIS, ptr) => {
            if ptr != Heap::CON && ho_list(ptr, heap) {
                return true;
            }
        }
        _ => (),
    }
    false
}
