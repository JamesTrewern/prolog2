use crate::{interface::{parser::{parse_literals, tokenise}, state::{Config, State}}, program::clause::{Clause, ClauseType}};



#[test]
fn body_pred() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["dad(adam,james)", "mum(tami,james)"] {
        let clause = Clause::parse_clause(parse_literals(&tokenise(clause)).unwrap(), &mut state.heap);
        state.prog.add_clause(clause, &state.heap)
    }
    state.heap.query_space = true;
    state.handle_directive(&tokenise("body_pred(dad,2),body_pred(mum,2)")).unwrap();
    let body_clauses: Vec<String> = state
        .prog
        .clauses
        .iter(&[ClauseType::BODY])
        .map(|i| state.prog.clauses.get(i).to_string(&state.heap))
        .collect();

    assert_eq!(body_clauses.len(),["mum(tami,james)", "dad(adam,james)"].len());
    for bc in body_clauses{
        assert!(["mum(tami,james)".to_string(), "dad(adam,james)".to_string()].contains(&bc))
    }
}


#[test]
fn max_h_pred() {
    let mut state = State::new(Some(Config::new().max_h_preds(0)));
    state.parse_prog(":- max_h_preds(1).".to_string());
    assert_eq!(state.config.max_h_pred, 1);
    state.parse_prog(":- max_h_preds(10).".to_string());
    assert_eq!(state.config.max_h_pred, 10);
    state.parse_prog(":- max_h_preds(0).".to_string());
    assert_eq!(state.config.max_h_pred, 0);
}

#[test]
fn max_h_clause() {
    let mut state = State::new(Some(Config::new().max_h_clause(0)));
    state.parse_prog(":- max_h_clause(1).".to_string());
    assert_eq!(state.config.max_h_clause, 1);
    state.parse_prog(":- max_h_clause(10).".to_string());
    assert_eq!(state.config.max_h_clause, 10);
    state.parse_prog(":- max_h_clause(0).".to_string());
    assert_eq!(state.config.max_h_clause, 0);
}

#[test]
fn share_preds() {
    let mut state = State::new(Some(Config::new().share_preds(false)));
    assert_eq!(state.config.share_preds, false);
    state.parse_prog(":- share_preds(true).".to_string());
    assert_eq!(state.config.share_preds, true);
    state.parse_prog(":- share_preds(false).".to_string());
    assert_eq!(state.config.share_preds, false);
}

#[test]
fn debug() {
    let mut state = State::new(Some(Config::new().debug(false)));
    assert_eq!(state.config.debug, false);
    state.parse_prog(":- debug(true).".to_string());
    assert_eq!(state.config.debug, true);
    state.parse_prog(":- debug(false).".to_string());
    assert_eq!(state.config.debug, false);
}