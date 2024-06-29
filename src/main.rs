#[cfg(test)]
mod examples;
mod heap;
mod interface;
mod pred_module;
mod program;
mod resolution;
use std::{collections::HashMap, process::ExitCode, sync::atomic::AtomicUsize};
use std::sync::atomic::Ordering::{Acquire, Relaxed};

use heap::store::Store;
use interface::{
    parser::{parse_goals, tokenise},
    state::{self, State},
};
use program::program::DynamicProgram;
use resolution::solver::Proof;
// use resolution::solver::Proof;
/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/


fn setup<'a>(file: &str, goal: &str) -> (State, Store<'a>, Vec<usize>) {
    // let mut state = State::new(None);
    // state.load_file(file).unwrap();
    // let mut store = Store::new(state.heap.read_slice().unwrap());
    // let goals: Vec<usize> = parse_goals(&tokenise(goal))
    //     .unwrap()
    //     .into_iter()
    //     .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
    //     .collect();
    // (state,store,goals)
    todo!()
}




fn main() -> ExitCode {

    // let (state,store,goals) = setup(
    //     "./examples/family",
    //     "ancestor(ken,james), ancestor(christine,james).",
    // );

    // let proof = Proof::new(
    //     &goals,
    //     store,
    //     DynamicProgram::new(None, state.program.read().unwrap()),
    //     None,
    //     &state
    // );


    let mut state = State::new(None);
    state.main_loop();
    ExitCode::SUCCESS
}
