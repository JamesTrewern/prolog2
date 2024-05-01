use std::collections::HashMap;

use crate::heap::Heap;

#[test]
fn add_str_1(){
    let mut heap = Heap::new(10);
    let structure = "p(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::REFC, 2),
        (Heap::REFC, 3)
    ]);

}
#[test]
fn add_str_2(){
    let mut heap = Heap::new(10);
    let structure = "P(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::REFC, 1),
        (Heap::REFC, 2),
        (Heap::REFC, 3)
    ]);
}
#[test]
fn add_str_3(){
    let mut heap = Heap::new(10);
    let structure = "P(Q(x),Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR,1),
        (Heap::REFC, 1),
        (Heap::CON,Heap::CON_PTR),
        (Heap::STR, 2),
        (Heap::REFC, 5),
        (Heap::REF, 0),
        (Heap::REFC, 7)
    ]);
}
#[test]
fn add_str_4(){
    let mut heap = Heap::new(10);
    let structure = "P([x,y])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::CON,Heap::CON_PTR),
        (Heap::LIS, 2),
        (Heap::CON,Heap::CON_PTR+1),
        (Heap::LIS, Heap::CON),
        (Heap::STR, 1),
        (Heap::REFC, 0),
        (Heap::LIS, 0)
    ]);
}
#[test]
fn add_str_5(){
    let mut heap = Heap::new(10);
    let structure = "P([p(x,y)])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR, 2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::CON, Heap::CON_PTR+1),
        (Heap::CON, Heap::CON_PTR+2),
        (Heap::REF, 0),
        (Heap::LIS, Heap::CON),
        (Heap::STR, 1),
        (Heap::REFC, 7),
        (Heap::LIS,4)
    ]);
}
#[test]
fn add_str_6(){
    let mut heap = Heap::new(10);
    let structure = "P(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec!["X","Y"]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::REFC, 1),
        (Heap::REFA, 2),
        (Heap::REFA, 3)
    ]);
}
#[test]
fn add_str_7(){
    let mut heap = Heap::new(10);
    let structure = "P([p(X,Y)])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec!["X","Y"]);
    assert_eq!(heap.term_string(addr),structure);
    assert_eq!(heap[..],[
        (Heap::STR, 2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::REFA, 2),
        (Heap::REFA, 3),
        (Heap::REF, 0),
        (Heap::LIS, Heap::CON),
        (Heap::STR, 1),
        (Heap::REFC, 7),
        (Heap::LIS,4)
    ]);
}