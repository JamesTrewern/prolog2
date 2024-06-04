//Broad test on example files to prove working state of application

use std::collections::HashMap;

use crate::{
    interface::{
        parser::{parse_goals, tokenise},
        state::{Config, State},
    },
    resolution::solver::Proof,
};

#[test]
fn ancestor() {
    let mut state = State::new(Some(
        Config::new().max_h_clause(4).max_h_preds(0).debug(false),
    ));

    state.load_file("./examples/family");


    let goals: Vec<usize> = parse_goals(&tokenise("ancestor(ken,james), ancestor(christine,james)"))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
    .collect();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        // println!("Hypothesis[{proofs}]");
        // for clause in branch.iter(){
        //     println!("{clause}");
        // }
        proofs += 1;
    }

    assert!(proofs > 0);
}

#[test]
fn map(){
    let mut state = State::new(Some(
        Config::new().max_h_clause(0).max_h_preds(0).debug(true),
    ));

    state.load_file("./examples/map");


    let goals: Vec<usize> = parse_goals(&tokenise("map([1],[2], X)."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
    .collect();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]");
        for clause in branch.iter(){
            println!("{clause}");
        }
        proofs += 1;
    }

    assert!(proofs > 0);
}

