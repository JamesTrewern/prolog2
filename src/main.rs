#[cfg(test)]
mod examples;
mod heap;
mod interface;
mod pred_module;
mod program;
mod resolution;
use std::{collections::HashMap, process::ExitCode};

use heap::store::Store;
use interface::{parser::{parse_goals, tokenise}, state::State};
use program::dynamic_program::{DynamicProgram, Hypothesis};
use resolution::solver::Proof;
// use resolution::solver::Proof;
/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/

fn setup<'a>(file: &str) -> State {
    let state = State::new(None);
    state.load_file(file).unwrap();
    state
}

fn make_goals<'a>(state: &'a State, goals: &str) -> (Vec<usize>, Store<'a>) {
    let mut store = Store::new(state.heap.try_read().unwrap());
    let goals: Vec<usize> = parse_goals(&tokenise(goals))
        .unwrap()
        .into_iter()
        .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
        .collect();
    (goals, store)
}

fn main() -> ExitCode {
    let state = setup("./examples/robots/robots");

    let (goals, store) = make_goals(&state, "test.");
    // let (goals, store) = make_goals(&state, "double_move(X,Y,Z).");


    let proof = Proof::new(
        &goals,
        store,
        Hypothesis::None,
        None,
        &state,
    );

    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);

    let state = State::new(None);
    state.main_loop();
    ExitCode::SUCCESS
}
