#[cfg(test)]
mod examples;
mod heap;
mod interface;
mod pred_module;
mod program;
mod resolution;

use std::{collections::HashMap, process::ExitCode};

use heap::store::Store;
use interface::{
    config::Config,
    parser::{parse_goals, tokenise},
    state,
};
use program::program::DynamicProgram;
use resolution::solver::Proof;
// use resolution::solver::Proof;
/*

Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/


fn setup(file: &str, goal: &str) -> Proof {
    state::start(None);
    state::load_file(file).unwrap();
    println!("loaded: {file}");
    let mut store = Store::new();
    let goals: Vec<usize> = parse_goals(&tokenise(goal))
        .unwrap()
        .into_iter()
        .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
        .collect();
    println!("{goals:?}");
    Proof::new(&goals, store, DynamicProgram::new(None), None)
}



fn main() -> ExitCode {

    let proof = setup(
        "./examples/family",
        "ancestor(ken,james), ancestor(christine,james).",
    );
    println!("proof");
    let mut proofs = 0;
    for _ in proof {
        proofs += 1;
    }
    assert!(proofs > 0);


    state::start(None);
    state::main_loop();


    ExitCode::SUCCESS
}
