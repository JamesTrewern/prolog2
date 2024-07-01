use fsize::fsize;
use std::{collections::HashMap, f64::consts::PI, mem};

use crate::{
    heap::{
        store::{Store, Tag},
        symbol_db::SymbolDB,
    },
    interface::term::Term,
};

#[test]
fn build_simple_term() {
let mut heap = Vec::new();
    let p = SymbolDB::set_const("p");
    let term = Term::STR(
        [
            Term::CON("p".into()),
            Term::VAR("X".into()),
            Term::VAR("Y".into()),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), false);
    assert_eq!(
        &heap[..],
        &[(Tag::Func, 3), (Tag::Con, p), (Tag::Ref, 2), (Tag::Ref, 3),]
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap[4..],
        &[(Tag::Func, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 1),]
    );
}

#[test]
fn build_simple_term_duplicate_var() {
let mut heap = Vec::new();
    let p = SymbolDB::set_const("p");
    let term = Term::STR(
        [
            Term::CON("p".into()),
            Term::VAR("X".into()),
            Term::VAR("X".into()),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), false);
    assert_eq!(
        &heap[..],
        &[(Tag::Func, 3), (Tag::Con, p), (Tag::Ref, 2), (Tag::Ref, 2),]
    );

    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap[4..],
        &[(Tag::Func, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 0),]
    );
}

#[test]
fn build_meta_term() {
let mut heap = Vec::new();
    let term = Term::STR(
        [
            Term::VAR("P".into()),
            Term::VARUQ("X".into()),
            Term::VARUQ("Y".into()),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap,
        &[
            (Tag::Func, 3),
            (Tag::Arg, 0),
            (Tag::ArgA, 1),
            (Tag::ArgA, 2),
        ]
    );
}

#[test]
fn build_term_with_substr() {
let mut heap = Vec::new();
    let term = Term::STR(
        [
            Term::VAR("P".into()),
            Term::VARUQ("X".into()),
            Term::STR([Term::VAR("Q".into()), Term::VARUQ("Y".into())].into()),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap,
        &[
            (Tag::Func, 2),
            (Tag::Arg, 0),
            (Tag::ArgA, 1),
            (Tag::Func, 3),
            (Tag::Arg, 2),
            (Tag::ArgA, 3),
            (Tag::Str, 0),
        ]
    );
}

#[test]
fn build_term_with_list() {
let mut heap = Vec::new();
    let p = SymbolDB::set_const("p");
    let term = Term::STR(
        [
            Term::CON("p".into()),
            Term::LIS([Term::VAR("X".into()), Term::VAR("Y".into())].into(), false),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap,
        &[
            (Tag::Arg, 0),
            (Tag::Lis, 2),
            (Tag::Arg, 1),
            Store::EMPTY_LIS,
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Lis, 0),
        ]
    );
}

#[test]
fn build_term_with_list_explicit_tail() {
let mut heap = Vec::new();
    let p = SymbolDB::set_const("p");
    let term = Term::STR(
        [
            Term::CON("p".into()),
            Term::LIS(
                [
                    Term::VAR("X".into()),
                    Term::VAR("Y".into()),
                    Term::VAR("Z".into()),
                ]
                .into(),
                true,
            ),
        ]
        .into(),
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap,
        &[
            (Tag::Arg, 0),
            (Tag::Lis, 2),
            (Tag::Arg, 1),
            (Tag::Arg, 2),
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Lis, 0),
        ]
    );
}

#[test]
fn build_naked_list() {
let mut heap = Vec::new();
    let term = Term::LIS([Term::VAR("X".into()), Term::VAR("Y".into())].into(), false);
    term.build_to_heap(&mut heap, &mut HashMap::new(), false);
    assert_eq!(
        &heap,
        &[
            (Tag::Ref, 0),
            (Tag::Lis, 2),
            (Tag::Ref, 2),
            Store::EMPTY_LIS,
            (Tag::Lis, 0),
        ]
    );

    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap[5..],
        &[
            (Tag::Arg, 0),
            (Tag::Lis, 7),
            (Tag::Arg, 1),
            Store::EMPTY_LIS,
            (Tag::Lis, 5),
        ]
    );
}

#[test]
fn build_int_list() {
let mut heap = Vec::new();
    let term = Term::LIS(
        [Term::INT(-1), Term::INT(-5), Term::INT(5), Term::INT(10)].into(),
        false,
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), true);
    assert_eq!(
        &heap,
        &[
            (Tag::Int, unsafe { mem::transmute_copy(&(-1 as isize)) }),
            (Tag::Lis, 2),
            (Tag::Int, unsafe { mem::transmute_copy(&(-5 as isize)) }),
            (Tag::Lis, 4),
            (Tag::Int, unsafe { mem::transmute_copy(&(5 as isize)) }),
            (Tag::Lis, 6),
            (Tag::Int, unsafe { mem::transmute_copy(&(10 as isize)) }),
            Store::EMPTY_LIS,
            (Tag::Lis, 0),
        ]
    );
}

#[test]
fn build_flt_list() {
    let mut heap = Vec::new();
    let term = Term::LIS(
        [
            Term::FLT(0.0),
            Term::FLT(-1.1),
            Term::FLT(5.0),
            Term::FLT(PI as fsize),
        ]
        .into(),
        false,
    );
    term.build_to_heap(&mut heap, &mut HashMap::new(), false);
    assert_eq!(
        &heap,
        &[
            (Tag::Flt, unsafe { mem::transmute_copy(&(0.0 as fsize)) }),
            (Tag::Lis, 2),
            (Tag::Flt, unsafe { mem::transmute_copy(&(-1.1 as fsize)) }),
            (Tag::Lis, 4),
            (Tag::Flt, unsafe { mem::transmute_copy(&(5.0 as fsize)) }),
            (Tag::Lis, 6),
            (Tag::Flt, unsafe { mem::transmute_copy(&(PI as fsize)) }),
            Store::EMPTY_LIS,
            (Tag::Lis, 0),
        ]
    );
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
