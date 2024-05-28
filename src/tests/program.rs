// use crate::{
//     clause::{self, *},
//     parser::{parse_goals, tokenise},
//     state::Config,
//     State,
// };

// #[test]
// fn call_con_head() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["p(X,Y):-q(X,Y)"] {
//         let clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("p(A,B)"), &mut state.heap).unwrap()[0];
//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 1);
//     for choice in choices {
//         assert_eq!(
//             choice.binding,
//             [(choice.clause + 2, goal + 2), (choice.clause + 3, goal + 3)]
//         )
//     }
// }

// #[test]
// fn call_fact() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["p(x,y)"] {
//         let clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("p(A,B)"), &mut state.heap).unwrap()[0];
//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 1);
//     for choice in choices {
//         assert_eq!(
//             choice.binding,
//             [(goal + 2, choice.clause + 2), (goal + 3, choice.clause + 3)]
//         )
//     }
// }

// #[test]
// fn call_meta_with_con() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["P(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
//         let clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("p(a,B,[c])"), &mut state.heap).unwrap()[0];
//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 1);
//     let choice = &choices[0];
//     assert_eq!(
//         choice.binding,
//         [
//             (choice.clause + 1, goal + 1),
//             (choice.clause + 2, goal + 2),
//             (choice.clause + 3, goal + 3),
//             (choice.clause + 4, goal + 4)
//         ]
//     )
// }

// #[test]
// fn call_unkown_no_match() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["p(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
//         let clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("p(A,B)"), &mut state.heap).unwrap()[0];
//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 0);
// }

// #[test]
// fn call_with_var_match_meta_and_body() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["P(X,Y):-Q(X,Y)\\X,Y", "p(X,Y):-q(X)"] {
//         let mut clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         if clause.clause_type == ClauseType::CLAUSE {
//             clause.clause_type = ClauseType::BODY
//         } 
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("P(A,B)"), &mut state.heap).unwrap()[0];

//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 2);

//     let choice = &choices[0];
//     let head = state.prog.clauses.get(choice.clause)[0];
//     assert_eq!(
//         choice.binding,
//         [
//             (head + 1, goal + 1),
//             (head + 2, goal + 2),
//             (head + 3, goal + 3)
//         ]
//     );

//     let choice = &choices[1];
//     let head = state.prog.clauses.get(choice.clause)[0];
//     assert_eq!(
//         choice.binding,
//         [
//             (goal + 1, head + 1),
//             (head + 2, goal + 2),
//             (head + 3, goal + 3)
//         ]
//     );
// }

// #[test]
// fn call_con_head_meta() {
//     let mut state = State::new(None);
//     state.heap.query_space = false;
//     for clause in ["p(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
//         let clause = Clause::parse_clause(&tokenise(clause), &mut state.heap).unwrap();
//         state.prog.add_clause(clause)
//     }
//     state.heap.query_space = true;
//     let goal = parse_goals(&tokenise("p(a,B,[c])"), &mut state.heap).unwrap()[0];

//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 1);
//     let choice = &choices[0];
//     assert_eq!(
//         choice.binding,
//         [
//             (choice.clause + 2, goal + 2),
//             (choice.clause + 3, goal + 3),
//             (choice.clause + 4, goal + 4)
//         ]
//     )
// }

// #[test]
// fn call_list_load_file() {}

// #[test]
// fn max_invented_predicates() {
//     let mut state = State::new(Some(Config::new().max_h_preds(0)));
//     state.heap.query_space = false;
//     let clause = Clause::parse_clause(&tokenise("P(X,Y):-Q(X,Y)\\X,Y"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     state.heap.query_space = true;
//     state.prog.clauses.sort_clauses();
//     state.prog.clauses.find_flags();
//     let goal = parse_goals(&tokenise("P(A,B)"), &mut state.heap).unwrap()[0];

//     let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 0);
// }

// #[test]
// fn max_predicates_0() {
//     let mut state = State::new(Some(Config::new().max_h_preds(0)));
//     state.heap.query_space = false;
//     let clause = Clause::parse_clause(&tokenise("P(X,Y):-Q(X,Y)\\X,Y"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     state.heap.query_space = true;
//     state.prog.clauses.sort_clauses();
//     state.prog.clauses.find_flags();
//     let goal = parse_goals(&tokenise("P(a,b)"), &mut state.heap).unwrap()[0];

//     let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 0);
// }

// #[test]
// fn max_predicates_1() {
//     let mut state = State::new(Some(Config::new().max_h_preds(1)));
//     state.heap.query_space = false;
//     let clause = Clause::parse_clause(&tokenise("P(X,Y):-Q(X,Y)\\X,Y"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     let clause = Clause::parse_clause(&tokenise("P(X):-Q(X)\\X"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     state.heap.query_space = true;
//     state.prog.clauses.sort_clauses();
//     state.prog.clauses.find_flags();

//     let goal1 = parse_goals(&tokenise("P(a,b)"), &mut state.heap).unwrap()[0];

//     let choices = &mut state.prog.call(goal1, &mut state.heap, &mut state.config);
//     choices.first_mut().unwrap().choose(&mut state);


//     let goal2 = parse_goals(&tokenise("P(a)"), &mut state.heap).unwrap()[0];
//     let choices = &mut state.prog.call(goal2, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 0);
// }

// #[test]
// fn max_clause_0() {
//     let mut state = State::new(Some(Config::new().max_h_clause(0)));
//     state.heap.query_space = false;
//     let clause = Clause::parse_clause(&tokenise("P(X,Y):-Q(X,Y)\\X,Y"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     state.heap.query_space = true;
//     state.prog.clauses.sort_clauses();
//     state.prog.clauses.find_flags();
//     let goal = parse_goals(&tokenise("P(a,b)"), &mut state.heap).unwrap()[0];

//     let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 0);
// }

// #[test]
// fn test_constraint() {
//     let mut state = State::new(Some(Config::new().max_h_clause(1).max_h_preds(0)));
//     state.heap.query_space = false;
//     let clause = Clause::parse_clause(&tokenise("P(X,Y):-Q(X,Y)\\X,Y"), &mut state.heap).unwrap();
//     state.prog.add_clause(clause);
//     let mut clause = Clause::parse_clause(&tokenise("q(a,b)"), &mut state.heap).unwrap();
//     clause.clause_type = ClauseType::BODY;
//     state.prog.add_clause(clause);
//     state.heap.query_space = true;
//     state.prog.organise_clause_table(&state.heap);
//     let mut goal = parse_goals(&tokenise("p(a,b)"), &mut state.heap).unwrap()[0];
//     let choice = &mut state.prog.call(goal, &mut state.heap, &mut state.config)[0];
//     goal = choice.choose(&mut state).0[0];
//     state.heap.print_heap();
//     println!("Goal: {goal}");
//     let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
//     assert!(choices.len() == 1);
// }
