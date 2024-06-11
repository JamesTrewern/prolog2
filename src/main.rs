mod resolution;
mod heap;
mod pred_module;
mod program;
mod interface;
mod tests;

use std::{collections::HashMap, process::ExitCode};

use interface::{config::Config, parser::{parse_goals, tokenise}, state::State};
use resolution::solver::Proof;
/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {

    let mut state = State::new(Some(
        Config::new().debug(false).max_depth(10),
    ));

    state.load_file("./examples/odd_even");


    let goals: Vec<usize> = parse_goals(&tokenise("even(4), not(even(3))."))
    .unwrap()
    .into_iter()
    .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
    .collect();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        proofs += 1;
    }

    assert!(proofs > 0);



    let mut state = State::new(Some(Config::new()));

    // state.main_loop();

    ExitCode::SUCCESS
}
