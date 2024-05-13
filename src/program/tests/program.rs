use std::collections::HashMap;

use crate::{clause::*, state::Config, Heap, Program, State};

#[test]
fn load_file_family() {
    let mut prog = Program::new();
    let mut heap = Heap::new(60);
    prog.load_file("examples/family", &mut heap)
}

#[test]
fn call_con_head() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["p(X,Y):-q(X,Y)"] {
        let (ct, c) = Clause::parse_clause("p(X,Y):-q(X,Y)", &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("p(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 1);
    let choice = &choices[0];
    for choice in choices {
        assert_eq!(
            choice.binding,
            [(choice.clause + 2, goal + 2), (choice.clause + 3, goal + 3)]
        )
    }
}

#[test]
fn call_fact() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["p(x,y)"] {
        let (ct, c) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("p(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 1);
    for choice in choices {
        assert_eq!(
            choice.binding,
            [(goal + 2, choice.clause + 2), (goal + 3, choice.clause + 3)]
        )
    }
}

#[test]
fn call_meta_with_con() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["P(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
        let (ct, c) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("p(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 1);
    let choice = &choices[0];
    assert_eq!(
        choice.binding,
        [
            (choice.clause + 1, goal + 1),
            (choice.clause + 2, goal + 2),
            (choice.clause + 3, goal + 3),
            (choice.clause + 4, goal + 4)
        ]
    )
}

#[test]
fn call_unkown_no_match() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["p(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
        let (ct, c) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("q(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 0);
}

#[test]
fn call_with_var_match_meta_and_body() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["P(X,Y):-Q(X,Y)\\X,Y", "p(X,Y):-q(X)"] {
        let (ct, c) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(
            if ct == ClauseType::CLAUSE {
                ClauseType::BODY
            } else {
                ct
            },
            c,
        )
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("P(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 2);

    let choice = &choices[0];
    let head = state.prog.clauses.get(choice.clause).1[0];
    assert_eq!(
        choice.binding,
        [
            (head + 1, goal + 1),
            (head + 2, goal + 2),
            (head + 3, goal + 3)
        ]
    );

    let choice = &choices[1];
    let head = state.prog.clauses.get(choice.clause).1[0];
    assert_eq!(
        choice.binding,
        [
            (goal + 1, head + 1),
            (head + 2, goal + 2),
            (head + 3, goal + 3)
        ]
    );
}

#[test]
fn call_con_head_meta() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["p(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
        let (ct, c) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state.heap.build_literal("p(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len() == 1);
    let choice = &choices[0];
    assert_eq!(
        choice.binding,
        [
            (choice.clause + 2, goal + 2),
            (choice.clause + 3, goal + 3),
            (choice.clause + 4, goal + 4)
        ]
    )
}

#[test]
fn call_list_load_file() {}

#[test]
fn max_invented_predicates() {
    let mut state = State::new(Some(Config::new().max_invented(0)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    let mut goal = state.heap.build_literal("P(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len()==0);
}

#[test]
fn max_clause_predicates() {
    let mut state = State::new(Some(Config::new().max_invented(0)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    let mut goal = state.heap.build_literal("p(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len()==0);
}


#[test]
fn test_constraint() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    let mut goal = state.heap.build_literal("p(a,b)", &mut HashMap::new(), &mut vec![]);
    let choice = &mut state.prog.call(goal, &mut state.heap, &state.config)[0];
    goal = choice.choose(&mut state).unwrap().0[0];
    let choices = state.prog.call(goal, &mut state.heap, &state.config);
    assert!(choices.len()==0);
}
