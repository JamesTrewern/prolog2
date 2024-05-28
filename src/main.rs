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
    let mut state = State::new(Some(Config::new().max_h_clause(2).max_h_preds(0).debug(true)));

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

    state.handle_directive(&tokenise("ancestor(adam,james)"));
    ExitCode::SUCCESS
}
