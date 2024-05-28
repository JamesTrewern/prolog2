use std::collections::HashMap;

use crate::{
    heap::heap::{Heap, Tag},
    interface::parser::{parse_literals, tokenise},
    resolution::unification::Binding,
};

#[test]
fn should_update_ref() {
    let mut heap = Heap::new(2);
    heap.set_var(None, false);
    let mut binding = Binding::new();
    binding.push((0, 1));
    heap.bind(&binding)
}

#[test]
#[should_panic]
fn should_not_update_ref() {
    let mut heap = Heap::new(2);
    heap.set_var(Some(1), false);
    heap.set_var(None, false);
    let mut binding = Binding::new();
    binding.push((0, 0));
    heap.bind(&binding);
}

#[test]
fn should_not_update_refc() {
    let mut heap = Heap::new(2);
    heap.query_space = true;
    heap.set_var(None, false);
    let mut binding = Binding::new();
    binding.push((0, 1));
    heap.bind(&binding);
    heap[0] = (Tag::REFC, 0);
}

#[test]
fn should_not_update_refa() {
    let mut heap = Heap::new(2);
    heap.query_space = true;
    heap.set_var(None, true);
    let mut binding = Binding::new();
    binding.push((0, 1));
    heap.bind(&binding);
    heap[0] = (Tag::REFA, 0);
}

#[test]
fn should_not_panic_print_heap() {
    let mut heap = Heap::new(100);
    for term in [
        "p(A,B)",
        "X == [1,2,3]",
        "P(Q([X,Y]))",
        "Z is X**2/Y**2",
        "R(Z)",
    ] {
        let tokens = tokenise(term);
        let term = parse_literals(&tokens).unwrap().remove(0);
        term.build_on_heap(&mut heap, &mut HashMap::new());
    }

    heap.print_heap();
}

#[test]
fn deref_addr() {
    let mut heap = Heap::new(100);
    heap.push((Tag::REF, 1));
    heap.push((Tag::REF, 2));
    heap.push((Tag::REF, 3));
    heap.push((Tag::REF, 3));
    assert_eq!(heap.deref_addr(0), 3)
}

#[test]
fn deref_addr_con() {
    let mut heap = Heap::new(100);
    heap.push((Tag::REF, 1));
    heap.push((Tag::REF, 2));
    heap.push((Tag::REF, 3));
    heap.push((Tag::CON, 3));
    assert_eq!(heap.deref_addr(0), 3)
}
