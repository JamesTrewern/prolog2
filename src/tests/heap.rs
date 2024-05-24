use std::collections::HashMap;
use crate::{heap::Tag, parser::{parse_literals, tokenise}, unification::*, Heap};

#[test]
fn should_update_ref(){
    let mut heap = Heap::new(2);
    heap.set_var(None, false);
    let binding:Binding = vec![(0,1)];
    heap.bind(&binding)
}

#[test]
#[should_panic]
fn should_not_update_ref(){
    let mut heap = Heap::new(2);
    heap.set_var(Some(1), false);
    heap.set_var(None, false);
    let binding:Binding = vec![(0,0)];
    heap.bind(&binding);
}

#[test]
fn should_not_update_refc(){
    let mut heap = Heap::new(2);
    heap.query_space = true;
    heap.set_var(None, false);
    let binding:Binding = vec![(0,1)];
    heap.bind(&binding);
    heap[0] = (Tag::REFC, 0);
}

#[test]
fn should_not_update_refa(){
    let mut heap = Heap::new(2);
    heap.query_space = true;
    heap.set_var(None, true);
    let binding:Binding = vec![(0,1)];
    heap.bind(&binding);
    heap[0] = (Tag::REFA, 0);
}

#[test]
fn should_not_panic_print_heap(){
    let mut heap = Heap::new(100);
    for term in ["p(A,B)", "X == [1,2,3]", "P(Q([X,Y]))", "Z is X**2/Y**2", "R(Z)"]{
        let tokens = tokenise(term);
        let term = parse_literals(&tokens).unwrap().remove(0);
        term.build_on_heap(&mut heap, &mut HashMap::new());
    }

    heap.print_heap();
}

#[test]
fn deref_addr(){
    let mut heap = Heap::new(100);
    heap.push((Tag::REF,1));
    heap.push((Tag::REF,2));
    heap.push((Tag::REF,3));
    heap.push((Tag::REF,3));
    assert_eq!(heap.deref_addr(0),3)
}

#[test]
fn deref_addr_con(){
    let mut heap = Heap::new(100);
    heap.push((Tag::REF,1));
    heap.push((Tag::REF,2));
    heap.push((Tag::REF,3));
    heap.push((Tag::CON,3));
    assert_eq!(heap.deref_addr(0),3)
}


// #[test]
// fn list_iterator_1(){
//     let mut heap = Heap::new(10);

//     let list = heap.build_literal("[X,y,Z]", &mut HashMap::new(), &vec![]);

//     todo!();
//     // let elements: Vec<((usize,usize),bool)> = heap.list_iterator(list).map(|(addr,tail)| (heap[addr],tail)).collect();

//     // assert!(elements.iter().all(|(_,tail)| !tail));

//     // let elements: Vec<(usize,usize)> = elements.iter().map(|(cell,tail)| cell.clone()).collect();

//     // assert_eq!(&elements, &[
//     //     (Tag::REF, 0),
//     //     (Tag::CON, Heap::CON_PTR),
//     //     (Tag::REF, 4)
//     // ])
// }

// #[test]
// fn list_iterator_2(){
//     let mut heap = Heap::new(10);

//     let list = heap.build_literal("[x,y|Z]", &mut HashMap::new(), &vec![]);

//     todo!();
//     // let elements: Vec<((usize,usize),bool)> = heap.list_iterator(list).map(|(addr,tail)| (heap[addr],tail)).collect();

//     // assert_eq!(&elements, &[
//     //     ((Tag::CON, Heap::CON_PTR),false),
//     //     ((Tag::CON, Heap::CON_PTR+1),false),
//     //     ((Tag::REF, 3),true)
//     // ])
// }