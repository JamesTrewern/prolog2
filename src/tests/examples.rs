//Broad test on example files to prove working state of application

use std::{collections::HashMap, fs};

use crate::{
    clause::{self, ClauseTraits, ClauseType}, parser::{parse_goals, tokenise}, solver::Proof, state::Config, State
};

#[test]
fn ancestor_1() {
    let mut state = State::new(Some(Config::new().max_h_clause(2).max_h_preds(0).debug(true)));

    state.load_file("./examples/family");

    // state.prog.write_prog(&state.heap);

    // let body_clauses: Vec<String> = state
    //     .prog
    //     .clauses
    //     .iter(&[ClauseType::BODY])
    //     .map(|c| c.1 .1.to_string(&state.heap))
    //     .collect();

    // for text in body_clauses{
    //     println!("{text}");
    // }

    let goals = parse_goals(&tokenise("ancestor(adam,james)"), &mut state.heap).unwrap();

    state.heap.print_heap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch}\n");
        proofs += 1;
    }
}

#[test]
fn ancestor_2() {
    let mut state = State::new(Some(
        Config::new().max_h_clause(4).max_h_preds(0).debug(false),
    ));

    state.load_file("./examples/family");

    let goals = parse_goals(&tokenise("ancestor(ken,james), ancestor(christine,james)"), &mut state.heap).unwrap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch}\n");
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

    let goals = parse_goals(&tokenise("dad(ken,adam)"), &mut state.heap).unwrap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch}\n");
        proofs += 1;
    }

    assert!(proofs > 0);
}
