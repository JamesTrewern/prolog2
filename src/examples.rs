// //Broad test on example files to prove working state of application

use std::collections::HashMap;

use crate::{
    heap::store::Store,
    interface::{
        parser::{parse_goals, tokenise},
        state::State,
    },
    program::program::{DynamicProgram, ProgH},
    resolution::solver::Proof,
};

fn setup<'a>(file: &str) -> State {
    let state = State::new(None);
    state.load_file(file).unwrap();
    state
}

fn make_goals<'a>(state: &'a State, goals: &str) -> (Vec<usize>, Store<'a>) {
    let mut store = Store::new(state.heap.try_read_slice().unwrap());
    let goals: Vec<usize> = parse_goals(&tokenise(goals))
        .unwrap()
        .into_iter()
        .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
        .collect();
    (goals, store)
}
#[test]
fn ancestor() {
    let state = setup("./examples/family");
    let (goals, store) = make_goals(&state, "ancestor(ken,james), ancestor(christine,james).");

    let proof = Proof::new(
        &goals,
        store,
        ProgH::None,
        None,
        &state,
    );

    println!("proof");
    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);
}

#[test]
fn map() {
    let state = setup("./examples/map");

    let (goals, store) = make_goals(&state, "map([1,2,3],[2,4,6], X).");
    let proof = Proof::new(
        &goals,
        store,
        ProgH::None,
        None,
        &state,
    );

    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);
}

#[test]
fn odd_even() {
    let state = setup("./examples/odd_even");

    let (goals, store) = make_goals(&state, "even(4), not(even(3)).");

    let proof = Proof::new(
        &goals,
        store,
        ProgH::None,
        None,
        &state,
    );

    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);
}

#[test]
fn top_prog() {
    let state = setup("./examples/top_prog");

    let (goals, store) = make_goals(&state, "test.");

    let proof = Proof::new(
        &goals,
        store,
        ProgH::None,
        None,
        &state,
    );

    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);
}

// #[test]
// fn move_up(){
//     let mut state = State::new(Some(
//         Config::new().max_h_clause(0).max_h_preds(0).debug(true).max_depth(10),
//     ));

//     state.load_file("./examples/move_up");

//     state.prog.print_prog(&state.heap);

//     let goals: Vec<usize> = parse_goals(&tokenise("move_up([1,5],[1,6])."))
//     .unwrap()
//     .into_iter()
//     .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
//     .collect();

//     let proof = Proof::new(&goals, &mut state);

//     let mut proofs = 0;
//     for branch in proof {
//         proofs += 1;
//     }

//     assert!(proofs > 0);
// }
