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

    let goals = parser::parse_goals(&tokenise("ancestor(adam,james)"), &mut state.heap).unwrap();

    state.heap.print_heap();

    let proof = Proof::new(&goals, &mut state);

    let mut proofs = 0;
    for branch in proof {
        println!("Hypothesis[{proofs}]: {branch:?}\n");
        proofs += 1;
    }
    ExitCode::SUCCESS
}
