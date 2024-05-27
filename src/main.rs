mod choice;
mod clause;
mod clause_table;
mod heap;
mod parser;
mod pred_module;
mod program;
mod solver;
mod state;
mod symbol_db;
mod term;
mod tests;
mod unification;

pub(crate) use heap::Heap;
use parser::{parse_literals, tokenise};
pub(crate) use program::Program;
use solver::Proof;
use state::Config;
pub(crate) use state::State;
use std::{collections::HashMap, process::ExitCode};

/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new(Some(
        Config::new()
            .max_h_clause(4)
            .max_h_preds(1)
            .debug(true)
            .max_depth(10),
    ));

    state.load_file("./examples/family");

    let goals: Box<[usize]> = parse_literals(&tokenise("ancestor(ken,james), ancestor(christine,james)"))
        .unwrap()
        .into_iter()
        .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new())).collect();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch:?}\n");
        proofs += 1;
    }
    ExitCode::SUCCESS
}
