use manual_rwlock::MrwLock;

use crate::{
    heap::{
        heap::Heap,
        store::{Cell, Store},
    },
    interface::parser::{parse_clause, tokenise},
    program::{clause::ClauseType, clause_table::ClauseTable},
};

fn setup<'a>() -> (MrwLock<Vec<Cell>>, ClauseTable) {
    let mut heap = Vec::new();
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

    (MrwLock::new(heap), clause_table)
}

#[test]
fn test_ordering() {
    let (empty, clause_table) = setup();
    let heap = Store::new(empty.read_slice().unwrap());
    let expected_order = ["a", "b", "c", "d", "e", "f"];
    for i in 0..clause_table.len() {
        let clause_string = &heap.term_string(clause_table[i][0])[..1];
        assert_eq!(clause_string, expected_order[i])
    }
}

#[test]
fn test_type_flags() {
    let (_, mut clause_table) = setup();
    assert_eq!(clause_table.find_flags(), [0, 2, 4, 6])
}

#[test]
fn complex_ordering() {
    let mut heap = Vec::new();
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
    let expected_order = ["a", "a", "a", "b", "c", "d", "e", "f", "g"];

    let lock = MrwLock::new(heap);

    let store = Store::new(lock.read_slice().unwrap());

    for i in 0..clause_table.len() {
        let clause_string = &store.term_string(clause_table[i][0])[..1];
        assert_eq!(clause_string, expected_order[i])
    }
}
