mod resolution;
mod heap;
mod pred_module;
mod program;
mod interface;
mod tests;

use std::process::ExitCode;

use interface::{parser::{self, tokenise}, state::{Config, State}};
use resolution::solver::Proof;

/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new(Some(Config::new()));

    state.main_loop();

    ExitCode::SUCCESS
}
