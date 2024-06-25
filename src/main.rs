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
fn main() -> ExitCode {
    // state::start(None);
    // state::load_file("examples/odd_even");

    state::start(None);
    state::load_file("./examples/family").unwrap();
    let mut store = Store::new();
    Config::set_max_depth(5);
    // let prog = PROGRAM.read().unwrap();
    // for i in 0..prog.len(){
    //     println!("{}",prog.get(i).to_string(&store))
    // }

    let goals: Vec<usize> =
        parse_goals(&tokenise("ancestor(ken,james), ancestor(christine,james)"))
            .unwrap()
            .into_iter()
            .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
            .collect();

    let proof = Proof::new(&goals, store, DynamicProgram::new(None), None);

    for _ in proof {
    }

    state::main_loop();


    ExitCode::SUCCESS
}
