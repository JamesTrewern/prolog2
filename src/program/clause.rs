use crate::{heap::Heap, unification::{unify, unify_rec}};

pub type Clause = [usize];

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum ClauseType {
    CONSTRAINT,
    CLAUSE,
    BODY,
    META,
    HYPOTHESIS,
}

pub trait ClauseTraits {
    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool;
    fn pred_symbol(&self, heap: &Heap) -> usize;
    fn higher_order(&self, heap: &Heap) -> bool;
    fn write_clause(&self, heap: &Heap);
    fn to_string(&self, heap: &Heap) -> String;
    fn deallocate(&self, heap: &mut Heap);
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

    fn to_string(&self, heap: &Heap) -> String {
        if self.len() == 1 {
            let clause_str = heap.term_string(self[0]);
            clause_str
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
            buffer
        }
    }

    fn pred_symbol(&self, heap: &Heap) -> usize {
        heap[self[0]].0
    }

    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool {
        //TO DO
        //Implement proper Subsumtption
        if self.len() == other.len() {
            let mut binding = match unify(self[0], other[0], heap) {
                Some(b) => b,
                None => return false,
            };
            for i in 1..self.len() {
                if !unify_rec(self[i], other[i], heap, &mut binding) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
    
    fn deallocate(&self, heap: &mut Heap) {
        for str_addr in self.iter().rev(){
            heap.deallocate_str(*str_addr);
        }
    }
}


//TO DO remove this and return HO? from build literal
fn ho_struct(addr: usize, heap: &Heap) -> bool {
    let arity = match heap[addr]{
        (Heap::STR, arity) => arity,
        _ => panic!("Literal ptr does not point to strucutre")
    };

    
    if Heap::REFC < heap[addr+1].0 {
        return true;
    }
    for i in 2..arity + 2 {
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
        (Heap::REFA, _) => true,
        (Heap::STR, _) => ho_struct(addr, heap),

        (Heap::LIS, ptr) => ptr != Heap::CON && ho_list(ptr, heap),
        (Heap::CON | Heap::INT, _) => false,
        _ => ho_struct(addr, heap),
    }
}


