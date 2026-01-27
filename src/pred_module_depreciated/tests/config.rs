// use crate::{
//     interface::{
//         config::Config, parser::{parse_goals, tokenise}, state::State
//     },
//     program::clause::{Clause, ClauseType},
// };

use crate::{
    heap::store::Store,
    interface::{
        config::Config,
        parser::{parse_clause, tokenise},
        state::State,
    },
    program::dynamic_program::{DynamicProgram, Hypothesis},
};

#[test]
fn body_pred() {
    let state = State::new(None);
    let mut prog = state.program.write().unwrap();
    for clause in ["dad(adam,james)", "mum(tami,james)"] {
        let clause = parse_clause(&tokenise(clause)).unwrap();
        prog.add_clause(
            clause.to_heap(&mut *state.heap.try_write().unwrap()),
            &*state.heap.try_read().unwrap(),
        );
    }
    prog.organise_clause_table(&*state.heap.try_read().unwrap());
    drop(prog);

    state
        .handle_directive(&tokenise("body_pred(dad,2),body_pred(mum,2)"))
        .unwrap();

    let store = Store::new(state.heap.try_read().unwrap());
    let prog = DynamicProgram::new(Hypothesis::None, state.program.read().unwrap());

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

#[test]
fn background_knowledge() {
    let state = State::new(None);
    let mut prog = state.program.write().unwrap();
    for clause in ["dad(adam,james)", "mum(tami,james)"] {
        let clause = parse_clause(&tokenise(clause)).unwrap();
        prog.add_clause(
            clause.to_heap(&mut *state.heap.try_write().unwrap()),
            &*state.heap.try_read().unwrap(),
        );
    }
    prog.organise_clause_table(&*state.heap.try_read().unwrap());
    drop(prog);

    state
        .handle_directive(&tokenise("background_knowledge([dad/2,mum/2])."))
        .unwrap();

    let store = Store::new(state.heap.try_read().unwrap());
    let prog = DynamicProgram::new(Hypothesis::None, state.program.read().unwrap());

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

#[test]
fn max_h_pred() {
    let mut config = Config::new();
    config.max_h_pred = 0;
    let state = State::new(Some(config));
    state.parse_prog(":- max_h_preds(1).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_pred, 1);
    state.parse_prog(":- max_h_preds(10).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_pred, 10);
    state.parse_prog(":- max_h_preds(0).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_pred, 0);
}

#[test]
fn max_h_clause() {
    let mut config = Config::new();
    config.max_h_clause = 0;
    let state = State::new(Some(config));
    state.parse_prog(":- max_h_clause(1).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_clause, 1);
    state.parse_prog(":- max_h_clause(10).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_clause, 10);
    state.parse_prog(":- max_h_clause(0).".to_string());
    assert_eq!(state.config.read().unwrap().max_h_clause, 0);
}

#[test]
fn share_preds() {
    let mut config = Config::new();
    config.share_preds = false;
    let state = State::new(Some(config));
    assert_eq!(state.config.read().unwrap().share_preds, false);
    state.parse_prog(":- share_preds(true).".to_string());
    assert_eq!(state.config.read().unwrap().share_preds, true);
    state.parse_prog(":- share_preds(false).".to_string());
    assert_eq!(state.config.read().unwrap().share_preds, false);
}

#[test]
fn debug() {
    let mut config = Config::new();
    config.debug = false;
    let state = State::new(Some(config));
    assert_eq!(state.config.read().unwrap().debug, false);
    state.parse_prog(":- debug(true).".to_string());
    assert_eq!(state.config.read().unwrap().debug, true);
    state.parse_prog(":- debug(false).".to_string());
    assert_eq!(state.config.read().unwrap().debug, false);
}
