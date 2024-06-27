use std::collections::HashMap;

use crate::{
    heap::store::Store,
    interface::{config::Config, parser::{parse_clause, parse_goals, tokenise}, state::State},
    program::{
        clause::ClauseType,
        hypothesis::Hypothesis,
        program::{CallRes, DynamicProgram},
    },
};

fn setup<'a>() -> (Store<'a>, DynamicProgram<'a>) {

    let mut state = State::new(None);
    let mut store = Store::new(&[]);

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

    (store, DynamicProgram::new(None, state.program.read().unwrap()))
}

#[test]
fn iter_clause_body() {
    let (heap, prog) = setup();
    let expected = vec![
        "d(X,Y)".to_string(),
        "c(X,Y)".to_string(),
        "b(X,Y)".to_string(),
        "a(X,Y)".to_string(),
    ];
    for i in prog.iter([true, true, false, false]) {
        assert!(expected.contains(&heap.term_string(prog.get(i)[0])));
    }
}

#[test]
fn iter_body_meta_hypothesis() {
    let (heap, prog) = setup();
    let expected = vec![
        "g(X,Y)".to_string(),
        "f(X,Y)".to_string(),
        "e(X,Y)".to_string(),
        "d(X,Y)".to_string(),
        "c(X,Y)".to_string(),
    ];
    for i in prog.iter([false, true, true, true]) {
        assert!(
            expected.contains(&heap.term_string(prog.get(i)[0])),
            "failed on [{i}] {}",
            heap.term_string(prog.get(i)[0])
        );
    }
}

#[test]
fn iter_meta_hypothesis() {
    let (heap, clause_table) = setup();
    let expected = vec![
        "g(X,Y)".to_string(),
        "f(X,Y)".to_string(),
        "e(X,Y)".to_string(),
    ];
    for i in clause_table.iter([false, false, true, true]) {
        assert!(expected.contains(&heap.term_string(clause_table.get(i)[0])));
    }
}

#[test]
fn call_meta_with_con() {
    let mut state = State::new(None);
    let mut store = Store::new(&[]);
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
