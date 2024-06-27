// use crate::{
//     interface::{
//         config::Config, parser::{parse_goals, tokenise}, state::State
//     },
//     program::clause::{Clause, ClauseType},
// };

use crate::{
    heap::store::Store,
    interface::{
        parser::{parse_clause, tokenise},
        state::{self, State},
    },
    program::program::DynamicProgram,
};

#[test]
fn body_pred() {
    let mut state = State::new(None);
    let mut store = Store::new(&[]);
    let mut prog = state.program.write().unwrap();
    for clause in ["dad(adam,james)", "mum(tami,james)"] {
        let clause = parse_clause(&tokenise(clause)).unwrap();
        prog.add_clause(clause.to_heap(&mut store), &store);
    }
    prog.organise_clause_table(&store);
    drop(prog);
    state.to_static_heap(&mut store);
    let prog = DynamicProgram::new(None, state.program.read().unwrap());
    state.handle_directive(&tokenise("body_pred(dad,2),body_pred(mum,2)")).unwrap();
    let body_clauses: Vec<String> = prog
        .iter([false, true, false, false])
        .map(|i| prog.get(i).to_string(&store))
        .collect();

    assert_eq!(
        body_clauses.len(),
        ["mum(tami,james)", "dad(adam,james)"].len()
    );
    for bc in body_clauses {
        assert!(["mum(tami,james)".to_string(), "dad(adam,james)".to_string()].contains(&bc))
    }
}

// #[test]
// fn max_h_pred() {
//     let mut state = State::new(Some(Config::new().max_h_preds(0)));
//     state.parse_prog(":- max_h_preds(1).".to_string());
//     assert_eq!(state.config.max_h_pred, 1);
//     state.parse_prog(":- max_h_preds(10).".to_string());
//     assert_eq!(state.config.max_h_pred, 10);
//     state.parse_prog(":- max_h_preds(0).".to_string());
//     assert_eq!(state.config.max_h_pred, 0);
// }

// #[test]
// fn max_h_clause() {
//     let mut state = State::new(Some(Config::new().max_h_clause(0)));
//     state.parse_prog(":- max_h_clause(1).".to_string());
//     assert_eq!(state.config.max_h_clause, 1);
//     state.parse_prog(":- max_h_clause(10).".to_string());
//     assert_eq!(state.config.max_h_clause, 10);
//     state.parse_prog(":- max_h_clause(0).".to_string());
//     assert_eq!(state.config.max_h_clause, 0);
// }

// #[test]
// fn share_preds() {
//     let mut state = State::new(Some(Config::new().share_preds(false)));
//     assert_eq!(state.config.share_preds, false);
//     state.parse_prog(":- share_preds(true).".to_string());
//     assert_eq!(state.config.share_preds, true);
//     state.parse_prog(":- share_preds(false).".to_string());
//     assert_eq!(state.config.share_preds, false);
// }

// #[test]
// fn debug() {
//     let mut state = State::new(Some(Config::new().debug(false)));
//     assert_eq!(state.config.debug, false);
//     state.parse_prog(":- debug(true).".to_string());
//     assert_eq!(state.config.debug, true);
//     state.parse_prog(":- debug(false).".to_string());
//     assert_eq!(state.config.debug, false);
// }
