mod choice;
mod clause_table;
mod clause;
mod heap;
mod unification;
mod program;
mod solver;
mod state;
mod tests;
mod symbol_db;
mod pred_module;

use std::{collections::HashMap, process::ExitCode, vec};
pub (crate) use heap::Heap;
pub (crate) use program::Program;
use solver::Proof;
pub (crate) use state::State;




/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new(None);

    state.load_file("examples/ancestor.pl");

    let goal1 = state.heap.build_literal("ancestor(adam,james)", &mut HashMap::new(), &vec![]);

    // start_proof(vec![goal1], &mut state);s


    ExitCode::SUCCESS
}
