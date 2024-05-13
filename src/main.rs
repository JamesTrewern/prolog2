mod heap;
mod program;
mod solver;
mod state;
mod tests;

use std::{collections::HashMap, process::ExitCode, vec};
pub (crate) use heap::Heap;
pub (crate) use program::Program;
use solver::start_proof;
pub (crate) use state::State;
pub (crate) use program::clause;
pub (crate) use heap::unification::*;



/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new(None);

    state.prog.load_file("examples/ancestor.pl", &mut state.heap);

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);

    start_proof(vec![goal1], &mut state);


    ExitCode::SUCCESS
}
