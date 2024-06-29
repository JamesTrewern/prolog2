use std::{collections::HashMap, io::Empty};

use manual_rwlock::MrwLock;

use crate::{
    heap::store::{Cell, Store},
    interface::{config::Config, parser::{parse_clause, parse_goals, tokenise}, state::State},
    program::{
        clause::ClauseType,
        hypothesis::Hypothesis,
        program::{CallRes, DynamicProgram},
    },
};


fn setup<'a>() -> State {
    let empty: MrwLock<Vec<Cell>> = MrwLock::new(Vec::new());

    let mut state = State::new(None);
    let mut store = Store::new(empty.read_slice().unwrap());

    let clauses = [
        (ClauseType::META, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::META, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
    ];

    for (clause_type, clause_string) in clauses {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut store);
        clause.clause_type = clause_type;
        state.program.write().unwrap().add_clause(clause, &store)
    }

    state.to_static_heap(&mut store);
    state.program.write().unwrap().organise_clause_table(&store);

    let mut hypothesis = Hypothesis::new();
    for clause_string in [("g(X,Y)")] {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut store);
        clause.clause_type = ClauseType::HYPOTHESIS;
        hypothesis.add_h_clause(clause, &mut store);
    }

    drop(store);

    state
}

#[test]
fn iter_clause_body() {
    let state = setup();
    let store = Store::new(state.heap.read_slice().unwrap());
    let prog = DynamicProgram::new(None, state.program.read().unwrap());
    let expected = vec![
        "d(X,Y)".to_string(),
        "c(X,Y)".to_string(),
        "b(X,Y)".to_string(),
        "a(X,Y)".to_string(),
    ];
    for i in prog.iter([true, true, false, false]) {
        assert!(expected.contains(&store.term_string(prog.get(i)[0])));
    }
}

#[test]
fn iter_body_meta_hypothesis() {
    let state = setup();
    let store = Store::new(state.heap.read_slice().unwrap());
    let prog = DynamicProgram::new(None, state.program.read().unwrap());
    let expected = vec![
        "g(X,Y)".to_string(),
        "f(X,Y)".to_string(),
        "e(X,Y)".to_string(),
        "d(X,Y)".to_string(),
        "c(X,Y)".to_string(),
    ];
    for i in prog.iter([false, true, true, true]) {
        assert!(
            expected.contains(&store.term_string(prog.get(i)[0])),
            "failed on [{i}] {}",
            store.term_string(prog.get(i)[0])
        );
    }
}

#[test]
fn iter_meta_hypothesis() {
    let state = setup();
    let store = Store::new(state.heap.read_slice().unwrap());
    let prog = DynamicProgram::new(None, state.program.read().unwrap());
    let expected = vec![
        "g(X,Y)".to_string(),
        "f(X,Y)".to_string(),
        "e(X,Y)".to_string(),
    ];
    for i in prog.iter([false, false, true, true]) {
        assert!(expected.contains(&store.term_string(prog.get(i)[0])));
    }
}

#[test]
fn call_meta_with_con() {
    let empty: MrwLock<Vec<Cell>> = MrwLock::new(Vec::new());

    let mut state = State::new(None);
    let mut store = Store::new(empty.read_slice().unwrap());
    for clause in ["P(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
        let clause = parse_clause(&tokenise(clause)).unwrap().to_heap(&mut store);
        state.program.write().unwrap().add_clause(clause, &store);
    }

    state.to_static_heap(&mut store);

    let mut prog = DynamicProgram::new(None, state.program.read().unwrap());

    let goal = parse_goals(&tokenise("p(a,B,[c])")).unwrap()[0].build_to_heap(
        &mut store,
        &mut HashMap::new(),
        false,
    );

    if let CallRes::Clauses(mut choices) = prog.call(goal, &mut store, Config::get_config()) {
        if let Some(clause) = choices.next() {
            let clause = prog.get(clause);
        } else {
            panic!()
        }
    } else {
        panic!()
    }
}
