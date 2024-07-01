// // //Broad test on example files to prove working state of application

// use std::collections::HashMap;

// use crate::{
//     heap::store::Store,
//     interface::{
//         parser::{parse_goals, tokenise},
//         state::State,
//     },
//     program::program::DynamicProgram,
//     resolution::solver::Proof,
// };

// fn setup<'a>(file: &str, goal: &str) -> (State, Vec<usize>) {
//     let mut state = State::new(None);
//     state.load_file(file).unwrap();

//     let goals: Vec<usize> = parse_goals(&tokenise(goal))
//         .unwrap()
//         .into_iter()
//         .map(|t| t.build_to_heap(&mut store, &mut HashMap::new(), false))
//         .collect();
//     state.to_static_heap(&mut store);
//     (state)
// }

// #[test]
// fn ancestor() {
//     let (state,goals) = setup(
//         "./examples/family",
//         "ancestor(ken,james), ancestor(christine,james).",
//     );
//     let store = Store::new(state.heap.read_slice().unwrap());

//     let proof = Proof::new(
//         &goals,
//         store,
//         DynamicProgram::new(None, state.program.read().unwrap()),
//         None,
//         &state
//     );


//     println!("proof");
//     let mut proofs = 0;
//     for _ in proof {
//         proofs += 1;
//     }
//     assert!(proofs > 0);
// }

// #[test]
// fn map() {
//     let (state,goals) = setup("./examples/map", "map([1,2,3],[2,4,6], X).");
//     let store = Store::new(state.heap.read_slice().unwrap());
    
//     let proof = Proof::new(
//         &goals,
//         store,
//         DynamicProgram::new(None, state.program.read().unwrap()),
//         None,
//         &state
//     );
    
//     let mut proofs = 0;
//     for _ in proof {
//         proofs += 1;
//     }
//     assert!(proofs > 0);
// }

// #[test]
// fn odd_even() {
//     let (state,goals) = setup("./examples/odd_even", "even(4), not(even(3)).");
//     let store = Store::new(state.heap.read_slice().unwrap());

//     let proof = Proof::new(
//         &goals,
//         store,
//         DynamicProgram::new(None, state.program.read().unwrap()),
//         None,
//         &state
//     );
    
//     let mut proofs = 0;
//     for _ in proof {
//         proofs += 1;
//     }
//     assert!(proofs > 0);
// }

// // #[test]
// // fn move_up(){
// //     let mut state = State::new(Some(
// //         Config::new().max_h_clause(0).max_h_preds(0).debug(true).max_depth(10),
// //     ));

// //     state.load_file("./examples/move_up");

// //     state.prog.print_prog(&state.heap);

// //     let goals: Vec<usize> = parse_goals(&tokenise("move_up([1,5],[1,6])."))
// //     .unwrap()
// //     .into_iter()
// //     .map(|t| t.build_on_heap(&mut state.heap, &mut HashMap::new()))
// //     .collect();

// //     let proof = Proof::new(&goals, &mut state);

// //     let mut proofs = 0;
// //     for branch in proof {
// //         proofs += 1;
// //     }

// //     assert!(proofs > 0);
// // }
