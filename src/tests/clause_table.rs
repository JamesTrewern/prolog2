
use crate::{clause::*, clause_table::ClauseTable, parser::tokenise, Heap};

fn setup() -> (Heap, ClauseTable) {
    let mut heap = Heap::new(200);
    let mut clause_table = ClauseTable::new();

    let clauses = [
        (ClauseType::META, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::HYPOTHESIS, "g(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::META, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
    ];

    for (clause_type, clause_string) in clauses {
        let (_, clause) = Clause::parse_clause(&tokenise(&clause_string), &mut heap).unwrap();
        clause_table.add_clause(clause, clause_type)
    }

    (heap, clause_table)
}

#[test]
fn test_ordering() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses();
    let expected_order = [
        "a(X,Y)", "b(X,Y)", "c(X,Y)", "d(X,Y)", "e(X,Y)", "f(X,Y)", "g(X,Y)",
    ];
    for i in 0..clause_table.len() {
        let clause_string = heap.term_string(clause_table[i][0]);
        assert_eq!(clause_string, expected_order[i])
    }
}

#[test]
fn test_type_flags() {
    let (_, mut clause_table) = setup();
    clause_table.sort_clauses();
    clause_table.find_flags();
    assert_eq!(clause_table.type_flags, [0, 2, 4, 6])
}

#[test]
fn iter_clause_body() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses();
    clause_table.find_flags();
    let mut expected = vec!["d(X,Y)", "c(X,Y)", "b(X,Y)", "a(X,Y)"];
    for i in clause_table.iter(&[ClauseType::CLAUSE, ClauseType::BODY]) {
        assert_eq!(heap.term_string(clause_table[i][0]), expected.pop().unwrap());
    }
}

#[test]
fn iter_body_meta_hypothesis() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses();
    clause_table.find_flags();
    let mut expected = vec!["g(X,Y)","f(X,Y)","e(X,Y)","d(X,Y)", "c(X,Y)"];
    for i in clause_table.iter(&[ClauseType::BODY, ClauseType::META, ClauseType::HYPOTHESIS]) {
        assert_eq!(heap.term_string(clause_table[i][0]), expected.pop().unwrap());
    }
}

#[test]
fn iter_meta_hypothesis() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses();
    clause_table.find_flags();
    let mut expected = vec!["g(X,Y)","f(X,Y)","e(X,Y)"];
    for i in clause_table.iter(&[ClauseType::META, ClauseType::HYPOTHESIS]) {
        assert_eq!(heap.term_string(clause_table[i][0]), expected.pop().unwrap());
    }
}

#[test]
pub fn predicate_map(){
    todo!()
}