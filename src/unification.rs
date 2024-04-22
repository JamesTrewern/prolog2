use crate::{
    binding::{Binding, BindingTraits},
    heap::Heap,
};

fn unify_vars(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    // Create binding between vars
    match binding.bound(addr1) {
        Some(addr1) => unify_rec(addr1, addr2, heap, binding),
        None => {
            binding.push((addr1, addr2));
            true
        }
    }
}

//Unify ref cell with non ref cell
fn unify_ref(ref_addr: usize, non_ref_addr: usize, heap: &Heap, binding: &mut Binding) -> bool {
    match binding.bound(ref_addr) {
        Some(addr1) => {
            if addr1 >= Heap::CON_PTR {
                if addr1 == non_ref_addr {
                    true
                } else if heap[non_ref_addr] == (Heap::CON, addr1) {
                    binding.update_dangling_const(addr1, non_ref_addr);
                    true
                } else {
                    false
                }
            } else {
                unify_rec(addr1, non_ref_addr, heap, binding)
            }
        }
        None => {
            binding.push((ref_addr, non_ref_addr));
            true
        }
    }
}

fn unify_struct(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //Symbol, Arity 
    let (s1,a1) = heap[addr1]; 
    let (s2,a2) = heap[addr2];

    //Fail if arity doesn't match
    if a1 != a2 {
        return false;
    }

    // Is either symbol a pointer to heap 
    if s1 < Heap::CON_PTR && s2 < Heap::CON_PTR{
        if !unify_rec(s1, s2, heap, binding){
            return false;
        }
    }else if s1 < Heap::CON_PTR { 
        if !unify_ref(heap.deref(s1), s2, heap, binding){
            return false;
        }
    }else if s2 < Heap::CON_PTR{
        if !unify_ref(heap.deref(s2), s1, heap, binding){
            return false;
        }
    }

    for i in 1..heap[addr1].1 + 1 {
        if !unify_rec(addr1 + i, addr2 + i, heap, binding) {
            return false;
        }
    }

    true
}

fn unify_list(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //var head
    let p1 = heap[heap[addr1].1];
    let p2 = heap[heap[addr2].1];

    //const symbols don't match
    if p1.0 >= Heap::CON_PTR && p2.0 >= Heap::CON_PTR && p1.0 != p2.0 {}
    //recursively create binding
    true
}

pub fn unify_rec(mut addr1: usize, mut addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //addr 1 from
    //addr 2 to
    addr1 = heap.deref(addr1);
    addr2 = heap.deref(addr2);
    // println!("addr1: {addr1}, addr2: {addr2}");
    let cell1 = &heap[addr1];
    let cell2 = &heap[addr2];
    // println!("{cell1:?},{cell2:?}");

    match (cell1.0, cell2.0) {
        (Heap::REF | Heap::REFC | Heap::REFA, Heap::REF | Heap::REFC | Heap::REFA) => unify_vars(addr1, addr2, heap, binding),
        (Heap::REF | Heap::REFA | Heap::REFC, _) => unify_ref(addr1, addr2, heap, binding),
        (_, Heap::REF | Heap::REFA | Heap::REFC) => unify_ref(addr2, addr1, heap, binding),
        (Heap::STR, Heap::STR) => unify_struct(cell1.1, cell2.1, heap, binding),
        (Heap::LIS, Heap::LIS) => unify_list(cell1.1, cell2.1, heap, binding),
        (Heap::CON | Heap::INT | Heap::FLT, Heap::CON | Heap::INT | Heap::FLT) => cell1 == cell2,
        (Heap::CON | Heap::INT | Heap::FLT, _) => panic!("Undefined unifiction behaviour"),
        (_, Heap::CON | Heap::INT | Heap::FLT) => panic!("Undefined unifiction behaviour"),
        _ => unify_struct(addr1, addr2, heap, binding),
    }
}

pub fn unify(addr1: usize, addr2: usize, heap: &Heap) -> Option<Binding> {
    let mut binding: Binding = vec![];
    if unify_rec(addr1, addr2, heap, &mut binding) {
        Some(binding)
    } else {
        None
    }
}
