use std::{arch::x86_64, collections::HashMap};

use crate::{heap::Heap, unification::*};

use super::heap;


#[test]
fn build_clause_literal_with_substr(){
    let p = Heap::CON_PTR;
    let x = Heap::CON_PTR+1;
    // P(X,Q(Y)) \X
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 1),
        (Heap::REFC, 1),
        (Heap::REFA, 2),
        (Heap::STR, 2),
        (Heap::REFC, 4),
        (Heap::REFC, 5),
        (Heap::STR_REF, 0),
        (Heap::CON, p),
        (Heap::CON, x),
    ]);

    let mut binding: Binding = vec![(4,7),(5,8)];
    let (new_goal, constant) = build_str(&mut binding, 3, &mut heap, &mut Some(vec![]));

    assert_eq!(&heap[new_goal-3..], &[
        (Heap::STR, 1),
        (Heap::REF, new_goal-2),
        (Heap::REFC, new_goal-1),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, x),
        (Heap::STR_REF, new_goal-3)
    ])
}

#[test]
fn build_goal_with_sub_str(){
    let p = Heap::CON_PTR;
    let q = Heap::CON_PTR+1;
    let x = Heap::CON_PTR+2;
    let y = Heap::CON_PTR+3;

    // p(q(X,Y))
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::CON, q),
        (Heap::REFC, 2),
        (Heap::REFC, 3),
        (Heap::STR, 1),
        (Heap::CON, p),
        (Heap::STR_REF, 0),
        (Heap::CON, x),
        (Heap::CON, y),
    ]);

    let mut binding: Binding = vec![(2,7),(3,8)];

    let (new_goal, constant) = build_str(&mut binding, 4, &mut heap, &mut None);

    assert_eq!(&heap[new_goal-4..], &[
        (Heap::STR, 2),
        (Heap::CON, q),
        (Heap::CON, x),
        (Heap::CON, y),
        (Heap::STR, 1),
        (Heap::CON, p),
        (Heap::STR_REF, new_goal-4),
    ])
}

#[test]
fn unfify_const_structs(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, a),
        (Heap::CON, b),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, a),
        (Heap::CON, b),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[]);
}

#[test]
fn unfify_var_arguments_with_consts(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, a),
        (Heap::REF, 3),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::REF, 6),
        (Heap::CON, b),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(6,2),(3,7)]);
}

#[test]
fn unfify_var_arguments_consts(){
    let p = Heap::CON_PTR;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::REFC, 2),
        (Heap::REFC, 3),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::REF, 6),
        (Heap::REF, 7),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(2,6),(3,7)]);
}

#[test]
fn unfify_var_arguments_with_meta(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::REF, 1),
        (Heap::REFA, 2),
        (Heap::REFA, 3),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::REF, 6),
        (Heap::REF, 7),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(1,5),(2,6),(3,7)]);
}

#[test]
fn unfify_const_arguments_with_meta(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::REF, 1),
        (Heap::REFA, 2),
        (Heap::REFA, 3),
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, a),
        (Heap::CON, b),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(1,5),(2,6),(3,7)]);
}

#[test]
fn unfify_const_with_var_list(){
    let a = Heap::CON_PTR;
    let b = Heap::CON_PTR+1;
    let mut heap = Heap::from_slice(&[
        (Heap::LIS,1),
        (Heap::CON, a),
        (Heap::LIS, 3),
        (Heap::CON, b),
        Heap::EMPTY_LIS,
        (Heap::LIS, 6),
        (Heap::REF, 6),
        (Heap::LIS, 8),
        (Heap::REF, 8),
        (Heap::REF, 9),
    ]);

    let binding = unify(0, 5, &heap).unwrap();
    assert_eq!(&binding,&[(6,1),(8,3),(9,4)]);
}

#[test]
fn unfify_const_lists(){
    let a = Heap::CON_PTR;
    let b = Heap::CON_PTR+1;
    let mut heap = Heap::from_slice(&[
        (Heap::LIS,1),
        (Heap::CON, a),
        (Heap::LIS, 3),
        (Heap::CON, b),
        Heap::EMPTY_LIS,
        (Heap::LIS, 6),
        (Heap::CON, a),
        (Heap::LIS, 8),
        (Heap::CON, b),
        Heap::EMPTY_LIS
    ]);

    let binding = unify(0, 5, &heap).unwrap();
    assert_eq!(&binding,&[]);
}

#[test]
fn unfify_const_with_meta_list(){
    let a = Heap::CON_PTR;
    let b = Heap::CON_PTR+1;
    let mut heap = Heap::from_slice(&[
        (Heap::LIS,1),
        (Heap::CON, a),
        (Heap::LIS, 3),
        (Heap::CON, b),
        Heap::EMPTY_LIS,
        (Heap::LIS, 6),
        (Heap::REFA, 6),
        (Heap::LIS, 8),
        (Heap::REFA, 8),
        (Heap::REFA, 9),
    ]);

    let binding = unify(0, 5, &heap).unwrap();
    assert_eq!(&binding,&[(6,1),(8,3),(9,4)]);
}

#[test]
fn unify_ref_to_con_with_con(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Heap::STR, 2),
        (Heap::CON, p),
        (Heap::CON, a),
        (Heap::CON, b),
        (Heap::CON, p),
        (Heap::STR, 2),
        (Heap::REF, 4),
        (Heap::CON, a),
        (Heap::REF, 8),
    ]);

    let binding = unify(0, 5, &heap).unwrap();

    assert_eq!(&binding,&[(8,3)]);
}
 