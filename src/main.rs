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
use state::Config;
pub (crate) use state::State;




/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new(Some(
        Config::new().max_h_size(4).max_invented(1).debug(true).max_depth(10),
    ));

    state.load_file("./examples/family");

    let goal1 = state.heap.build_literal("ancestor(ken,james)", &mut HashMap::new(), &vec![]);
    let goal2 = state.heap.build_literal("ancestor(christine,james)", &mut HashMap::new(), &vec![]);

    let proof = Proof::new(&[goal1, goal2], &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch}\n");
        proofs += 1;
    }
    ExitCode::SUCCESS
}
