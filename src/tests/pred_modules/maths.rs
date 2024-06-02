use std::collections::HashMap;

use crate::{interface::{parser::{parse_literals, tokenise}, state::State}, resolution::solver::Proof};

fn setup() -> State{
    let mut state = State::new(None);
    state.load_module("maths");
    state
}

#[test]
fn test_not_eq(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("5 =/= 1."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_eq(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("5 =:= 5."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}


#[test]
fn test_is_eq(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("X is 1, X =:= 1."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_add_int(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("5 + 5 =:= 10 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_add_flt(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1.5 + 1.2 =:= 2.7 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_add_flt_int(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1 + 1.5 + 1.5 =:= 4 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_sub_with_neg_result(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1 - 1.5 =:= -0.5 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_sub_add(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1 - 1.5 + 1.5 =:= 1 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn test_div_by_neg(){
    let mut  state = setup();

    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1/-2.5 =:= -0.4 ."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}

#[test]
fn cos_sin_tan(){
    let mut  state = setup();
    let mut vars = HashMap::new();
    let goals: Vec<usize> = parse_literals(&tokenise("1 =:= round(acos(cos(1))), 1 =:= round(asin(sin(1))), 1 =:= round(atan(tan(1)))."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut vars))
    .collect();

    state.heap.print_heap();

    assert_eq!(Proof::new(&goals, &mut state).count(), 1);
}
