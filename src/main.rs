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


fn setup<'a>(file: &str, goal: &str) -> Proof<'a> {
    let mut state = State::new(None);
    state.load_file(file).unwrap();
    let mut store = Store::new(&[]);
    let goals: Vec<usize> = parse_goals(&tokenise(goal))
        .unwrap()
        .into_iter()
        .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
        .collect();
    Proof::new(
        &goals,
        store,
        DynamicProgram::new(None, state.program.read().unwrap()),
        None,
        &state
    )
}




fn main() -> ExitCode {

    let proof = setup("./examples/odd_even", "even(4), not(even(3)).");
    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);


    let mut state = State::new(None);
    state.main_loop();
    ExitCode::SUCCESS
}
