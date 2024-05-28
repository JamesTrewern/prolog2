use std::{collections::HashMap, f64::consts::PI, mem};
use fsize::fsize;

use crate::{heap::heap::{Heap, Tag}, interface::term::Term};


#[test]
fn build_simple_term(){
    let mut heap = Heap::new(100);
    let p = heap.add_const_symbol("p");
    let term = Term::STR([Term::CON("p".into()),Term::VAR("X".into()),Term::VAR("Y".into()),].into());
    term.build_on_heap(&mut heap, &mut HashMap::new());
    assert_eq!(&heap[..], &[
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REF, 2),
        (Tag::REF, 3),

    ]);
}

#[test]
fn build_simple_term_duplicate_var(){
    let mut heap = Heap::new(100);
    let p = heap.add_const_symbol("p");
    let term = Term::STR([Term::CON("p".into()),Term::VAR("X".into()),Term::VAR("X".into()),].into());
    term.build_on_heap(&mut heap, &mut HashMap::new());
    assert_eq!(&heap[..], &[
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REF, 2),
        (Tag::REF, 2),

    ]);
}

#[test]
fn build_meta_term(){
    let mut heap = Heap::new(100);
    let term = Term::STR([Term::VAR("P".into()),Term::VARUQ("X".into()),Term::VARUQ("Y".into()),].into());
    heap.query_space = false;
    term.build_on_heap(&mut heap, &mut HashMap::new());
    heap.query_space = true;
    assert_eq!(&heap[..], &[
        (Tag::STR, 2),
        (Tag::REFC, 1),
        (Tag::REFA, 2),
        (Tag::REFA, 3),

    ]);
}
#[test]
fn build_term_with_list(){
    let mut heap = Heap::new(100);
    let p = heap.add_const_symbol("p");
    let term = Term::STR([Term::CON("p".into()),Term::LIS([Term::VAR("X".into()),Term::VAR("Y".into())].into(),false)].into());
    heap.query_space = false;
    term.build_on_heap(&mut heap, &mut HashMap::new());
    heap.query_space = true;
    assert_eq!(&heap[..], &[
        (Tag::REFC, 0),
        (Tag::LIS, 2),
        (Tag::REFC, 2),
        Heap::EMPTY_LIS,
        (Tag::STR, 1),
        (Tag::CON, p),
        (Tag::LIS, 0),
    ]);
}

#[test]
fn build_term_with_list_explicit_tail(){
    let mut heap = Heap::new(100);
    let p = heap.add_const_symbol("p");
    let term = Term::STR([Term::CON("p".into()),Term::LIS([Term::VAR("X".into()),Term::VAR("Y".into()),Term::VAR("Z".into())].into(),true)].into());
    heap.query_space = false;
    term.build_on_heap(&mut heap, &mut HashMap::new());
    heap.query_space = true;
    assert_eq!(&heap[..], &[
        (Tag::REFC, 0),
        (Tag::LIS, 2),
        (Tag::REFC, 2),
        (Tag::REFC, 3),
        (Tag::STR, 1),
        (Tag::CON, p),
        (Tag::LIS, 0),
    ]);
}

#[test]
fn build_naked_list(){
    let mut heap = Heap::new(100);
    let term = Term::LIS([Term::VAR("X".into()),Term::VAR("Y".into())].into(),false);
    heap.query_space = false;
    term.build_on_heap(&mut heap, &mut HashMap::new());
    heap.query_space = true;
    assert_eq!(&heap[..], &[
        (Tag::REFC, 0),
        (Tag::LIS, 2),
        (Tag::REFC, 2),
        Heap::EMPTY_LIS,
    ]);
}

#[test]
fn build_int_list(){
    let mut heap = Heap::new(100);
    let term = Term::LIS([Term::INT(-1), Term::INT(-5), Term::INT(5), Term::INT(10)].into(), false);
    term.build_on_heap(&mut heap, &mut HashMap::new());
    assert_eq!(&heap[..], &[
        (Tag::INT, unsafe {mem::transmute_copy(&(-1 as isize))}),
        (Tag::LIS, 2),
        (Tag::INT, unsafe {mem::transmute_copy(&(-5 as isize))}),
        (Tag::LIS, 4),
        (Tag::INT, unsafe {mem::transmute_copy(&(5 as isize))}),
        (Tag::LIS, 6),
        (Tag::INT, unsafe {mem::transmute_copy(&(10 as isize))}),
        (Tag::LIS, Heap::CON_PTR),
    ]);
}

#[test]
fn build_flt_list(){
    let mut heap = Heap::new(100);
    let term = Term::LIS([Term::FLT(0.0), Term::FLT(-1.1), Term::FLT(5.0), Term::FLT(PI as fsize)].into(), false);
    term.build_on_heap(&mut heap, &mut HashMap::new());
    assert_eq!(&heap[..], &[
        (Tag::FLT, unsafe {mem::transmute_copy(&(0.0 as fsize))}),
        (Tag::LIS, 2),
        (Tag::FLT, unsafe {mem::transmute_copy(&(-1.1 as fsize))}),
        (Tag::LIS, 4),
        (Tag::FLT, unsafe {mem::transmute_copy(&(5.0 as fsize))}),
        (Tag::LIS, 6),
        (Tag::FLT, unsafe {mem::transmute_copy(&(PI as fsize))}),
        (Tag::LIS, Heap::CON_PTR),
    ]);
}

// #[test]
// fn json_build_simple_term(){
//     todo!()
// }

// #[test]
// fn json_build_meta_term(){
//     todo!()
// }
// #[test]
// fn json_build_term_with_list(){
//     todo!()
// }

// #[test]
// fn json_build_term_with_list_explicit_tail(){
//     todo!()
// }

// #[test]
// fn json_build_naked_list(){
//     todo!()
// }

// #[test]
// fn json_build_int_list(){
//     todo!()
// }

// #[test]
// fn json_build_flt_list(){
//     todo!()
// }