use crate::{heap::{Heap, Tag}, unification::*};



#[test]
fn build_clause_literal_with_substr(){
    let p = Heap::CON_PTR;
    let x = Heap::CON_PTR+1;
    // P(X,Q(Y)) \X
    let mut heap = Heap::from_slice(&[
        (Tag::STR, 1),
        (Tag::REFC, 1),
        (Tag::REFA, 2),
        (Tag::STR, 2),
        (Tag::REFC, 4),
        (Tag::REFC, 5),
        (Tag::StrRef, 0),
        (Tag::CON, p),
        (Tag::CON, x),
    ]);

    let mut binding: Binding = vec![(4,7),(5,8)];
    let (new_goal, _) = build_str(&mut binding, 3, &mut heap, &mut Some(vec![]));

    assert_eq!(&heap[new_goal-3..], &[
        (Tag::STR, 1),
        (Tag::REF, new_goal-2),
        (Tag::REFC, new_goal-1),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, x),
        (Tag::StrRef, new_goal-3)
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
        (Tag::STR, 2),
        (Tag::CON, q),
        (Tag::REFC, 2),
        (Tag::REFC, 3),
        (Tag::STR, 1),
        (Tag::CON, p),
        (Tag::StrRef, 0),
        (Tag::CON, x),
        (Tag::CON, y),
    ]);

    let mut binding: Binding = vec![(2,7),(3,8)];

    let (new_goal, constant) = build_str(&mut binding, 4, &mut heap, &mut None);

    assert_eq!(&heap[new_goal-4..], &[
        (Tag::STR, 2),
        (Tag::CON, q),
        (Tag::CON, x),
        (Tag::CON, y),
        (Tag::STR, 1),
        (Tag::CON, p),
        (Tag::StrRef, new_goal-4),
    ])
}

#[test]
fn unfify_const_structs(){
    let p = Heap::CON_PTR;
    let a = Heap::CON_PTR+1;
    let b = Heap::CON_PTR+2;
    let mut heap = Heap::from_slice(&[
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, a),
        (Tag::CON, b),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, a),
        (Tag::CON, b),
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
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, a),
        (Tag::REF, 3),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REF, 6),
        (Tag::CON, b),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(6,2),(3,7)]);
}

#[test]
fn unfify_var_arguments_consts(){
    let p = Heap::CON_PTR;
    let mut heap = Heap::from_slice(&[
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REFC, 2),
        (Tag::REFC, 3),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REF, 6),
        (Tag::REF, 7),
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
        (Tag::STR, 2),
        (Tag::REF, 1),
        (Tag::REFA, 2),
        (Tag::REFA, 3),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::REF, 6),
        (Tag::REF, 7),
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
        (Tag::STR, 2),
        (Tag::REF, 1),
        (Tag::REFA, 2),
        (Tag::REFA, 3),
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, a),
        (Tag::CON, b),
    ]);

    let binding = unify(0, 4, &heap).unwrap();
    assert_eq!(&binding,&[(1,5),(2,6),(3,7)]);
}

#[test]
fn unfify_const_with_var_list(){
    let a = Heap::CON_PTR;
    let b = Heap::CON_PTR+1;
    let mut heap = Heap::from_slice(&[
        (Tag::LIS,1),
        (Tag::CON, a),
        (Tag::LIS, 3),
        (Tag::CON, b),
        Heap::EMPTY_LIS,
        (Tag::LIS, 6),
        (Tag::REF, 6),
        (Tag::LIS, 8),
        (Tag::REF, 8),
        (Tag::REF, 9),
    ]);

    let binding = unify(0, 5, &heap).unwrap();
    assert_eq!(&binding,&[(6,1),(8,3),(9,4)]);
}

#[test]
fn unfify_const_lists(){
    let a = Heap::CON_PTR;
    let b = Heap::CON_PTR+1;
    let mut heap = Heap::from_slice(&[
        (Tag::LIS,1),
        (Tag::CON, a),
        (Tag::LIS, 3),
        (Tag::CON, b),
        Heap::EMPTY_LIS,
        (Tag::LIS, 6),
        (Tag::CON, a),
        (Tag::LIS, 8),
        (Tag::CON, b),
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
        (Tag::LIS,1),
        (Tag::CON, a),
        (Tag::LIS, 3),
        (Tag::CON, b),
        Heap::EMPTY_LIS,
        (Tag::LIS, 6),
        (Tag::REFA, 6),
        (Tag::LIS, 8),
        (Tag::REFA, 8),
        (Tag::REFA, 9),
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
        (Tag::STR, 2),
        (Tag::CON, p),
        (Tag::CON, a),
        (Tag::CON, b),
        (Tag::CON, p),
        (Tag::STR, 2),
        (Tag::REF, 4),
        (Tag::CON, a),
        (Tag::REF, 8),
    ]);

    let binding = unify(0, 5, &heap).unwrap();

    assert_eq!(&binding,&[(8,3)]);
}
 