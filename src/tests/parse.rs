use std::collections::HashMap;

use crate::heap::Heap;

#[test]
fn add_str_1(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "p(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    debug_assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::REFC, 2),
        (Heap::REFC, 3)
    ]);
}
#[test]
fn add_str_2(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    debug_assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::REFC, 1),
        (Heap::REFC, 2),
        (Heap::REFC, 3)
    ]);
}
#[test]
fn add_str_3(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P(Q(x),Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    debug_assert_eq!(heap.term_string(addr),structure);
    debug_assert_eq!(heap[..],[
        (Heap::STR,1),
        (Heap::REFC, 1),
        (Heap::CON,Heap::CON_PTR),
        (Heap::STR, 2),
        (Heap::REFC, 4),
        (Heap::STR_REF, 0),
        (Heap::REFC, 6)
    ]);
}
#[test]
fn add_str_4(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P([x,y])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    assert_eq!(heap.term_string(addr),structure);
    debug_assert_eq!(heap[..],[
        (Heap::CON,Heap::CON_PTR),
        (Heap::LIS, 2),
        (Heap::CON,Heap::CON_PTR+1),
        Heap::EMPTY_LIS,
        (Heap::STR, 1),
        (Heap::REFC, 5),
        (Heap::LIS, 0)
    ]);
}
#[test]
fn add_str_5(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P([p(x,y)])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec![]);
    debug_assert_eq!(heap.term_string(addr),structure);
    debug_assert_eq!(heap[..],[
        (Heap::STR, 2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::CON, Heap::CON_PTR+1),
        (Heap::CON, Heap::CON_PTR+2),
        (Heap::STR_REF, 0),
        Heap::EMPTY_LIS,
        (Heap::STR, 1),
        (Heap::REFC, 7),
        (Heap::LIS,4)
    ]);
}
#[test]
fn add_str_6(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P(X,Y)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec!["X","Y"]);
    assert_eq!(heap.term_string(addr),"P(∀'X,∀'Y)");
    debug_assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::REFC, 1),
        (Heap::REFA, 2),
        (Heap::REFA, 3)
    ]);
}
#[test]
fn add_str_7(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "P([p(X,Y)])";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &vec!["X","Y"]);
    assert_eq!(heap.term_string(addr),"P([p(∀'X,∀'Y)])");
    assert_eq!(heap[..],[
        (Heap::STR, 2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::REFA, 2),
        (Heap::REFA, 3),
        (Heap::STR_REF, 0),
        Heap::EMPTY_LIS,
        (Heap::STR, 1),
        (Heap::REFC, 7),
        (Heap::LIS,4)
    ]);
}

#[test]
fn build_float_and_int(){
    let mut heap = Heap::new(20);
    heap.query_space = false;
    let structure = "p(5,11.10)";
    let addr = heap.build_literal(structure, &mut HashMap::new(), &Vec::new());
    assert_eq!(heap.term_string(addr),"p(5,11.1)");
    debug_assert_eq!(heap[..],[
        (Heap::STR,2),
        (Heap::CON, Heap::CON_PTR),
        (Heap::INT, 5),
        (Heap::FLT, (11.1 as f64).to_bits() as usize)
    ]);
}

//TODO add number parsing tests