//Broad test on example files to prove working state of application

use std::collections::HashMap;

use crate::{
    interface::{
        parser::{parse_literals, tokenise},
        state::{Config, State},
    },
    resolution::solver::Proof,
};

#[test]
fn ancestor_1() {
    let mut state = State::new(Some(
        Config::new().max_h_clause(2).max_h_preds(0).debug(true),
    ));

    state.load_file("./examples/family");

    let goals: Vec<usize> = parse_literals(&tokenise("ancestor(adam,james)"))
        .unwrap()
        .into_iter()
        .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
        .collect();

    state.heap.print_heap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch:?}\n");
        proofs += 1;
    }

    assert!(proofs > 0)
}

#[test]
fn ancestor_2() {
    let mut state = State::new(Some(
        Config::new().max_h_clause(4).max_h_preds(0).debug(false),
    ));

    state.load_file("./examples/family");


    let goals: Vec<usize> = parse_literals(&tokenise("ancestor(ken,james), ancestor(christine,james)"))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
    .collect();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch:?}\n");
        proofs += 1;
    }

    assert!(proofs > 0);
}

#[test]
fn ancestor_3() {
    let mut state = State::new(Some(
        Config::new().max_h_clause(4).max_h_preds(0).debug(false),
    ));

    state.load_file("./examples/family");

    let goals: Vec<usize> = parse_literals(&tokenise("dad(ken,X)"))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
    .collect();

    state.heap.print_heap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch:?}\n");
        proofs += 1;
    }

    assert_eq!(proofs, 3);
}
