use std::{usize, vec};

use crate::{binding::{Binding, BindingTraits}, heap::Heap};

fn ref_tag(tag: usize) -> bool {
    tag == Heap::REF || tag == Heap::REFA
}

fn const_tag(tag: usize) -> bool {
    tag == Heap::CON || tag == Heap::INT
}

fn structure_tag(tag: usize) -> bool {
    tag == Heap::STR || tag == Heap::LIS
}

fn equal_consts(addr1: usize, addr2: usize, heap: &Heap) -> bool {
    //TO DO recursive comparison if structure
    heap[addr1] == heap[addr2]
}

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
            if addr1 >= isize::MAX as usize {
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
    //Fail if arity doesn't match
    if heap[addr1].1 != heap[addr2].1 {
        return false;
    }
    if heap[addr1].0 < isize::MAX as usize && heap[addr2].0 < isize::MAX as usize {
        // 2 Var symbols
        if !unify_vars(heap[addr1].0, heap[addr2].0, heap, binding) {
            return false;
        }
    } else if heap[addr1].0 < isize::MAX as usize {
        // left var symbol
        if !unify_ref(heap[addr1].0, heap[addr2].0, heap, binding) {
            return false;
        }
    } else if heap[addr2].0 < isize::MAX as usize {
        // right var symbol
        if !unify_ref(heap[addr2].0, heap[addr1].0, heap, binding) {
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
    if p1.0 >= isize::MAX as usize && p2.0 >= isize::MAX as usize && p1.0 != p2.0 {}
    //recursively create binding
    true
}

fn unify_rec(mut addr1: usize, mut addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //addr 1 goal
    //addr 2 clause
    addr1 = heap.deref(addr1);
    addr2 = heap.deref(addr2);
    let tag1 = heap[addr1].0;
    let tag2 = heap[addr2].0;

    if ref_tag(tag1) && ref_tag(tag2) {
        unify_vars(addr1, addr2, heap, binding)
    } else if ref_tag(tag1) && !ref_tag(tag2) {
        unify_ref(addr1, addr2, heap, binding)
    } else if !ref_tag(tag1) && ref_tag(tag2) {
        unify_ref(addr2, addr1, heap, binding)
    } else if tag1 < Heap::MIN_TAG as usize && tag2 < Heap::MIN_TAG {
        unify_struct(addr1, addr2, heap, binding)
    } else if tag1 == Heap::LIS && tag2 == Heap::LIS {
        unify_list(addr1, addr2, heap, binding)
    } else {
        if heap[addr1] == heap[addr2] {
            true
        } else {
            false
        }
    }
}

pub fn unify(mut addr1: usize, mut addr2: usize, heap: &Heap) -> Option<Binding> {
    let mut binding: Binding = vec![];
    if unify_rec(addr1, addr2, heap, &mut binding){
        Some(binding)
    }else{
        None
    }
}
