use std::collections::HashMap;
use crate::{unification::*, Heap};

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
    heap[0] = (Heap::REFC, 0);
}

#[test]
fn should_not_update_refa(){
    let mut heap = Heap::new(2);
    heap.query_space = true;
    heap.set_var(None, true);
    let binding:Binding = vec![(0,1)];
    heap.bind(&binding);
    heap[0] = (Heap::REFA, 0);
}

#[test]
fn build_literal_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let str3 = heap.build_literal("q(X,Y)", &mut HashMap::new(), &vec![]);
    let mut binding = unify(str1, str2, &heap).unwrap();
    heap.print_heap();

    let str4 = build_str_from_binding(&mut binding, str3, &mut heap, &mut None).unwrap();
}