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
        Config::new().max_h_clause(0).max_h_preds(0).debug(true).max_depth(10),
    ));

    state.load_file("examples/odd_even");

    state.main_loop();
    ExitCode::SUCCESS
}
