use std::collections::HashMap;

use crate::{
    heap::store::{Store, Tag},
    interface::parser::{parse_goals, tokenise},
};

// #[test]
// #[should_panic]
// fn should_not_update_ref() {
//     let mut heap = Store::new();
//     heap.set_ref(Some(1));
//     heap.set_ref(None);
//     let mut binding = Binding::new();
//     binding.push((0, 0));
//     heap.bind(&binding);
// }

#[test]
fn should_not_panic_print_heap() {
    let mut heap = Store::new();
    for term in [
        "p(A,B).",
        "X == [1,2,3].",
        "P(Q([X,Y])).",
        "Z is X**2/Y**2.",
        "R(Z).",
    ] {
        let tokens = tokenise(term);
        let term = parse_goals(&tokens).unwrap().remove(0);
        term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    }

    heap.print_heap();
}

#[test]
fn deref_addr() {
    let mut heap = Store::new();
    heap.push((Tag::Ref, 1));
    heap.push((Tag::Ref, 2));
    heap.push((Tag::Ref, 3));
    heap.push((Tag::Ref, 3));
    assert_eq!(heap.deref_addr(0), 3)
}

#[test]
fn deref_addr_con() {
    let mut heap = Store::new();
    heap.push((Tag::Ref, 1));
    heap.push((Tag::Ref, 2));
    heap.push((Tag::Ref, 3));
    heap.push((Tag::Con, 3));
    assert_eq!(heap.deref_addr(0), 3)
}
