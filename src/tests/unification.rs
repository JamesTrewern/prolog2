use std::collections::HashMap;

use crate::{binding, heap::Heap, unification::unify};
#[test]
fn unify_struct_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("P(X,Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (1,5),
            (2,6),
            (3,7),
        ])
    }
}
#[test]
fn unify_struct_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("P(q(X),Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(q(x),y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (4,11),
            (2,9),
            (6,13),
        ])
    }
}

#[test]
fn unify_struct_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,x)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,6),
        ])
    }
}
#[test]
fn unify_struct_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,Y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,6),
            (7,6)
        ])
    }
}

#[test]
fn unify_struct_5(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_struct_6(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("q(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_list_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("l([X,X])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("l([x,y])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_list_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("l([q(X),Y])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("l([q(x),y])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,12),
            (5,15),
        ])
    }
}

#[test]
fn unify_list_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("l([X,y|T])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("l([x,Y|T])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (0,7),
            (9,2),
            (3,10)
        ])
    }
}

#[test]
fn unify_list_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("l([q(X),Y|T])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("l([q(x),y|T])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,12),
            (5,15),
            (6,16),
        ])
    }
}

#[test]
fn unify_list_struct_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([x,y|T],z)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([x,y],Z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (3,11),
            (15,7),
        ])
    }
}

#[test]
fn unify_list_struct_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([x,y],z)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([],Z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
// TO DO implement reading this syntax for edge cases, for now this is not important
fn unify_list_struct_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([q(X),Y|[]])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([q(x),y])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,12),
            (5,15),
        ])
    }
}

#[test]
fn unify_list_struct_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([q(X),Y],Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([q(x),y],z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}