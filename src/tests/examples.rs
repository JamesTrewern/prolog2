//Broad test on example files to prove working state of application

use std::collections::HashMap;

use crate::{solver::start_proof, State};

#[test]
fn ancestor_1(){
    let mut state = State::new();

    state.prog.load_file("examples/ancestor.pl", &mut state.heap);

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);

    start_proof(vec![goal1], &mut state);
}

#[test]
fn ancestor_2(){
    let mut state = State::new();

    state.prog.load_file("examples/ancestor.pl", &mut state.heap);

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);
    let goal2 = state.heap.build_literal("ancestor(mum,james)", &mut HashMap::new(), &vec![]);


    start_proof(vec![goal1,goal2], &mut state);
}