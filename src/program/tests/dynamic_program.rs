use std::collections::HashMap;

use crate::{
    heap::store::Store,
    interface::{config::Config, parser::{parse_clause, parse_goals, tokenise}},
    program::{
        clause::ClauseType,
        hypothesis::Hypothesis,
        program::{CallRes, DynamicProgram, PROGRAM},
    },
};

fn setup() -> (Store, DynamicProgram) {
    let mut store = Store::new();
    let mut prog = PROGRAM.write().unwrap();

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
        prog.add_clause(clause, &store)
    }

    store.to_prog();
    prog.organise_clause_table(&store);

    let mut hypothesis = Hypothesis::new();
    for clause_string in [("g(X,Y)")] {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut store);
        clause.clause_type = ClauseType::HYPOTHESIS;
        hypothesis.add_h_clause(clause, &mut store);
    }

    (store, DynamicProgram::new(None))
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
    let mut store = Store::new();

    let mut prog = PROGRAM.write().unwrap();
    for clause in ["P(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
        let clause = parse_clause(&tokenise(clause)).unwrap().to_heap(&mut store);
        prog.add_clause(clause, &store);
    }

    store.to_prog();
    drop(prog);

    let mut prog = DynamicProgram::new(None);

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
