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
fn should_not_panic_print_heap(){
    let mut heap = Heap::new(100);
    // heap.build_literal("[X,Y,Z]", &mut HashMap::new(), &vec![]);
    // heap.build_literal("p([X,Y,Z])", &mut HashMap::new(), &vec![]);
    // heap.build_literal("P(x,y)", &mut HashMap::new(), &vec![]);
    heap.build_literal("P(x,Q(Y))", &mut HashMap::new(), &vec!["Y"]);
    // heap.build_literal("[X,Y,Z]", &mut HashMap::new(), &vec!["X","Y"]);

    heap.print_heap()
}

