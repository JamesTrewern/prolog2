//Broad test on example files to prove working state of application

use std::{collections::HashMap, fs};

use crate::{solver::start_proof, state::Config, State};

#[test]
fn ancestor_1(){
    let mut config = Config::new();
    config.max_clause = 2;
    config.max_invented = 0;
    let mut state = State::new(Some(config));

    state.prog.load_file("./examples/family", &mut state.heap);

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);

    assert!(start_proof(vec![goal1], &mut state));
    
}

#[test]
fn ancestor_2(){
    let mut config = Config::new();
    config.max_clause = 4;
    config.max_invented = 0;
    let mut state = State::new(Some(config));

    state.prog.load_file("./examples/family", &mut state.heap);

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);
    let goal2 = state.heap.build_literal("ancestor(mum,james)", &mut HashMap::new(), &vec![]);


    start_proof(vec![goal1,goal2], &mut state);
}