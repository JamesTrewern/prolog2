mod heap;
mod program;
mod solver;
mod unification;
mod state;
mod binding;
mod tests;

use std::{collections::HashMap, process::ExitCode, vec};

use binding::BindingTraits;
use heap::Heap;
use program::Program;

use solver::start_proof;
// use solver::start_proof;
use state::State;

use crate::unification::unify;




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

//TO DO P is bound twice resolve this;
fn main() -> ExitCode {
    let mut state = State::new();

    let str1 = state.heap.build_literal("P(X,Y)", &mut HashMap::new(), &vec![]);
    let str2 = state.heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding = unify(str1, str2, &state.heap);

    state.heap.print_heap();

    

    // start_proof(vec![goal1], &mut state);

    


    ExitCode::SUCCESS
}
