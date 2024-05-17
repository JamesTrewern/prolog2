//Broad test on example files to prove working state of application

use std::{collections::HashMap, fs};

use crate::{
    clause::{ClauseTraits, ClauseType},
    solver::Proof,
    state::Config,
    State,
};

#[test]
fn ancestor_1() {
    let mut config = Config::new();
    config.max_h_clause = 2;
    config.max_h_pred = 0;
    let mut state = State::new(Some(config));

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

    let goal1 = state
        .heap
        .build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);

    let mut proof = Proof::new(&[goal1], &mut state);

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

    let goal1 = state.heap.build_literal("ancestor(ken,james)", &mut HashMap::new(), &vec![]);
    let goal2 = state.heap.build_literal("ancestor(christine,james)", &mut HashMap::new(), &vec![]);

    let proof = Proof::new(&[goal1, goal2], &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch}\n");
        proofs += 1;
    }

    assert!(proofs > 0);
}
