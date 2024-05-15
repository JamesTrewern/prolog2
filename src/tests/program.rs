use std::collections::HashMap;

use crate::{clause::*, state::Config, Heap, Program, State};

#[test]
fn call_con_head() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["p(X,Y):-q(X,Y)"] {
        let (ct, c) = Clause::parse_clause("p(X,Y):-q(X,Y)", &mut state.heap);
        state.prog.add_clause(ct, c)
    }
    state.heap.query_space = true;
    let goal = state
        .heap
        .build_literal("p(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let goal = state
        .heap
        .build_literal("p(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let goal = state
        .heap
        .build_literal("p(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let goal = state
        .heap
        .build_literal("q(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let goal = state
        .heap
        .build_literal("P(A,B)", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let goal = state
        .heap
        .build_literal("p(a,B,[c])", &mut HashMap::new(), &mut vec![]);
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
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
    let mut goal = state
        .heap
        .build_literal("P(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
    assert!(choices.len() == 0);
}

#[test]
fn max_predicates_0() {
    let mut state = State::new(Some(Config::new().max_invented(0)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    let mut goal = state
        .heap
        .build_literal("P(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
    assert!(choices.len() == 0);
}

#[test]
fn max_predicates_1() {
    let mut state = State::new(Some(Config::new().max_invented(1)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    let (ct, c) = Clause::parse_clause("P(X):-Q(X)\\X", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    
    let goal1 = state
        .heap
        .build_literal("P(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal1, &mut state.heap, &mut state.config);
    choices.first_mut().unwrap().choose(&mut state);
    let goal2 = state
        .heap
        .build_literal("P(a)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal2, &mut state.heap, &mut state.config);
    assert!(choices.len() == 0);
}

#[test]
fn max_clause_0() {
    let mut state = State::new(Some(Config::new().max_h_size(0)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    let mut goal = state
        .heap
        .build_literal("p(a,b)", &mut HashMap::new(), &mut vec![]);
    let choices = &mut state.prog.call(goal, &mut state.heap, &mut state.config);
    assert!(choices.len() == 0);
}

#[test]
fn test_constraint() {
    let mut state = State::new(Some(Config::new().max_h_size(1).max_invented(0)));
    state.heap.query_space = false;
    let (ct, c) = Clause::parse_clause("P(X,Y):-Q(X,Y)\\X,Y", &mut state.heap);
    state.prog.add_clause(ct, c);
    let (_, c) = Clause::parse_clause("p(a,b)", &mut state.heap);
    state.prog.add_clause(ClauseType::BODY, c);
    state.heap.query_space = true;
    state.prog.clauses.sort_clauses();
    state.prog.clauses.find_flags();
    let mut goal = state
        .heap
        .build_literal("p(a,b)", &mut HashMap::new(), &mut vec![]);
    let choice = &mut state.prog.call(goal, &mut state.heap, &mut state.config)[0];
    goal = choice.choose(&mut state).unwrap().0[0];
    state.heap.print_heap();
    println!("Goal: {goal}");
    let choices = state.prog.call(goal, &mut state.heap, &mut state.config);
    assert!(choices.len() == 0);
}
