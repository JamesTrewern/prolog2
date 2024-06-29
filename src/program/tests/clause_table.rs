use std::io::Empty;

use manual_rwlock::MrwLock;

use crate::{
    heap::store::{Cell, Store},
    interface::parser::{parse_clause, tokenise},
    program::{clause::ClauseType, clause_table::ClauseTable},
};


fn setup<'a>() -> (MrwLock<Vec<Cell>>, ClauseTable) {
    let empty: MrwLock<Vec<Cell>> = MrwLock::new(Vec::new());
    let mut heap = Store::new(empty.read_slice().unwrap());
    let mut clause_table = ClauseTable::new();

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
            .to_heap(&mut heap);
        clause.clause_type = clause_type;
        clause_table.add_clause(clause)
    }
    clause_table.sort_clauses(&heap);

    drop(heap);

    (empty, clause_table)
}

#[test]
fn test_ordering() {
    let (empty, clause_table) = setup();
    let mut heap = Store::new(empty.read_slice().unwrap());
    let expected_order = ["a(X,Y)", "b(X,Y)", "c(X,Y)", "d(X,Y)", "e(X,Y)", "f(X,Y)"];
    for i in 0..clause_table.len() {
        let clause_string = heap.term_string(clause_table[i][0]);
        assert_eq!(clause_string, expected_order[i])
    }
}

#[test]
fn test_type_flags() {
    let (empty,mut clause_table) = setup();
    assert_eq!(clause_table.find_flags(), [0, 2, 4, 6])
}

#[test]
fn complex_ordering() {
    let EMPTY: MrwLock<Vec<Cell>> = MrwLock::new(Vec::new());
    let mut heap = Store::new(EMPTY.read_slice().unwrap());
    let mut clause_table = ClauseTable::new();

    let clauses = [
        (ClauseType::META, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::HYPOTHESIS, "g(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::META, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
        (ClauseType::CLAUSE, "a(a,b,c)"),
        (ClauseType::CLAUSE, "a(a,Z)"),
    ];

    for (clause_type, clause_string) in clauses {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut heap);
        clause.clause_type = clause_type;
        clause_table.add_clause(clause)
    }
    clause_table.sort_clauses(&heap);
    let expected_order = [
        "a(X,Y)", "a(a,Z)", "a(a,b,c)", "b(X,Y)", "c(X,Y)", "d(X,Y)", "e(X,Y)", "f(X,Y)", "g(X,Y)",
    ];
    for i in 0..clause_table.len() {
        let clause_string = heap.term_string(clause_table[i][0]);
        assert_eq!(clause_string, expected_order[i])
    }
}
