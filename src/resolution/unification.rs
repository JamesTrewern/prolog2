use std::ops::Deref;

use crate::heap::{heap::Heap, store::{Store, Tag}, symbol_db::SymbolDB};

/**Array of pair of memory addresses, binding from left to right  */
#[derive(Debug)]
pub struct Binding(pub Vec<(usize, usize)>);

impl Binding {
    pub fn new() -> Binding {
        Binding(Vec::new())
    }

    /**Is addr bound to some new value. Uses recursion to compute binding chains */
    pub fn bound(&self, addr: usize) -> Option<usize> {
        // println!("{addr}");
        match self.iter().find(|(a1, _)| *a1 == addr) {
            Some((_, a2)) => match self.bound(*a2) {
                Some(a2) => Some(a2),
                None => Some(*a2),
            },
            None => None,
        }
    }

    pub fn to_string(&self, heap: &Store) -> String {
        let mut buffer = String::from("{");
        for binding in self.iter() {
            if let Some(symbol) = SymbolDB::get_var(binding.0) {
                buffer += &symbol;
            } else {
                buffer += &format!("_{}", binding.0);
            }
            buffer += "/";
            if binding.1 < Store::CON_PTR {
                buffer += &heap.term_string(binding.1)
            } else {
                buffer += &SymbolDB::get_const(binding.1)
            };
            buffer += ",";
        }
        buffer.pop();
        buffer += "}";
        buffer
    }

    pub fn push(&mut self, bind: (usize, usize)) {
        self.0.push(bind)
    }
}

impl Deref for Binding {
    type Target = [(usize, usize)];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/**Unify two ref cells */
fn unify_vars(addr1: usize, addr2: usize, heap: &Store, binding: &mut Binding) -> bool {
    // Create binding between vars
    match binding.bound(addr1) {
        //If addr1 is already bound attempt to unfiy it's binding and addr 2
        Some(addr1) => unify(addr1, addr2, heap, binding),
        None => {
            binding.push((addr1, addr2));
            true
        }
    }
}

/**Unify ref cell with non ref cell
 * @ref_addr: heap address to reference cell
 * @non_ref_addr: heap address to a constant or structure cell
 */
fn unify_ref(ref_addr: usize, non_ref_addr: usize, heap: &Store, binding: &mut Binding) -> bool {
    match binding.bound(ref_addr) {
        Some(addr1) => {
            if addr1 == non_ref_addr {
                true
            } else {
                //if ref_addr is already bound attempt to unify it's binding with non-ref_addr
                unify(addr1, non_ref_addr, heap, binding)
            }
        }
        None => {
            //ref_addr is not bound so create binding from ref_addr to non_ref_addr
            binding.push((ref_addr, non_ref_addr));
            true
        }
    }
}

/**Unify two structures together */
fn unify_struct(addr1: usize, addr2: usize, heap: &Store, binding: &mut Binding) -> bool {
    //Arity
    let a1 = heap[addr1].1;
    let a2 = heap[addr2].1;

    //Fail if arity doesn't match
    if a1 != a2 {
        return false;
    }

    //iterate over struct terms including Pred/Func symbol
    for i in 1..=a1 + 1 {
        if !unify(addr1 + i, addr2 + i, heap, binding) {
            return false;
        }
    }

    true
}

/**Unfiy two lists together */
fn unify_list(addr1: usize, addr2: usize, heap: &Store, binding: &mut Binding) -> bool {
    //Check for empty list
    if addr1 == Store::CON_PTR && addr2 == Store::CON_PTR {
        return true;
    } else if addr1 == Store::CON_PTR || addr2 == Store::CON_PTR {
        return false;
    }
    //unify head and tail, if both succeed return true
    unify(addr1, addr2, heap, binding) && unify(addr1 + 1, addr2 + 1, heap, binding)
}

/**Branching point for unification of two cells. Uses tag of each cell to determine how to unify */
pub fn unify(addr1: usize, addr2: usize, heap: &Store, binding: &mut Binding) -> bool {
    //Firstly deref cells
    let (addr1, addr2) = (heap.deref_addr(addr1), heap.deref_addr(addr2));
    //TO DO check at this point if binding already exists as deref cell could have already been considered
    match (heap[addr1].0, heap[addr2].0) {
        (Tag::Ref | Tag::Arg | Tag::ArgA, Tag::Ref | Tag::Arg | Tag::ArgA) => {
            unify_vars(addr1, addr2, heap, binding)
        }
        (Tag::Ref | Tag::ArgA | Tag::Arg, _) => unify_ref(addr1, addr2, heap, binding),
        (_, Tag::Ref | Tag::ArgA | Tag::Arg) => unify_ref(addr2, addr1, heap, binding),
        (Tag::Func, Tag::Func) => unify_struct(addr1, addr2, heap, binding),
        (Tag::Lis, Tag::Lis) => unify_list(heap[addr1].1, heap[addr2].1, heap, binding),
        (Tag::Con | Tag::Int | Tag::Flt, Tag::Con | Tag::Int | Tag::Flt) => {
            heap[addr1] == heap[addr2]
        }
        // (Tag::CON | Tag::INT | Tag::FLT, _) => {
        //     panic!(
        //         "Undefined unifiction behaviour {addr1}:{:?}, {addr2}{:?}",
        //         heap[addr1], heap[addr2]
        //     )
        // }
        // (_, Tag::CON | Tag::INT | Tag::FLT) => panic!(
        //     "Undefined unifiction behaviour {addr1}:{:?}, {addr2}:{:?}",
        //     heap[addr1], heap[addr2]
        // ),
        _ => false,
    }
}

