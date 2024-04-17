mod heap;
mod program;
mod solver;
mod unification;
mod state;
mod binding;

use std::{collections::HashMap, io, os::macos::raw::stat, process::{Child, ExitCode}, vec};

use binding::BindingTraits;
use heap::Heap;
use program::Program;

use solver::start_proof;
// use solver::start_proof;
use state::State;
use unification::unify;



// pub fn main_loop() {
//     let mut state = State::new();
//     let mut buf = String::new();
//     loop {
//         // buf.clear();
//         io::stdin()
//             .read_line(&mut buf)
//             .expect("Error reading from console");

//         if buf.contains('.') {
//             let mut directive = buf.split('.').next().unwrap();
//             let goals = parse_goals(directive, &mut state.heap);
//             start_proof(goals, &mut state);
//             buf.clear();
//         }
//     }
// }

// fn parse_goals(input: &str, heap: &mut Heap) -> Vec<usize> {
//         let mut last_i: usize = 0;
//         let mut in_brackets = (0, 0);
//         let mut goals: Vec<usize> = vec![];
//         let mut symbols_map: HashMap<String, usize> = HashMap::new();
//         for (i, c) in input.chars().enumerate() {
//             match c {
//                 '(' => {
//                     in_brackets.0 += 1;
//                 }
//                 ')' => {
//                     if in_brackets.0 == 0 {
//                         break;
//                     }
//                     in_brackets.0 -= 1;
//                 }
//                 '[' => {
//                     in_brackets.1 += 1;
//                 }
//                 ']' => {
//                     if in_brackets.1 == 0 {
//                         break;
//                     }
//                     in_brackets.1 -= 1;
//                 }
//                 ',' => {
//                     if in_brackets == (0, 0) {
//                         goals.push(heap.build_literal(&input[last_i..i], &mut symbols_map, &vec![]));
//                         last_i = i + 1
//                     }
//                 }
//                 _ => (),
//             }
//         }
//         return goals;
// }

/*
Remove terms from heap when no longer needed
Store Heap index at query start
New Clause rules: constraints, head can't be existing predicate

*/
fn main() -> ExitCode {
    let mut state = State::new();

    state.prog.load_file("test", &mut state.heap);
    state.prog.write_prog(&state.heap);

    let goal = state.heap.build_literal("parent(adam,james)", &mut HashMap::new(), &vec![]);

    start_proof(vec![goal], &mut state);
    ExitCode::SUCCESS
}
