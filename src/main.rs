#[cfg(test)]
mod examples;
mod heap;
mod interface;
mod pred_module;
mod program;
mod resolution;
use std::process::ExitCode;

use interface::state::State;
// use resolution::solver::Proof;
/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/

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

    let state = State::new(None);
    state.main_loop();
    ExitCode::SUCCESS
}
