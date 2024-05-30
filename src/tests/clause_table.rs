use crate::{heap::heap::Heap, interface::parser::{parse_literals, tokenise}, program::{clause::{Clause, ClauseType}, clause_table::ClauseTable}};

fn setup() -> (Heap, ClauseTable) {
    let mut heap = Heap::new(200);
    let mut clause_table = ClauseTable::new();

    let clauses = [
        (ClauseType::HO, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::HYPOTHESIS, "g(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::HO, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
    ];

    for (clause_type, clause_string) in clauses {
        let mut clause = Clause::parse_clause(parse_literals(&tokenise(&clause_string)).unwrap(), &mut heap);
        clause.clause_type = clause_type;
        clause_table.add_clause(clause)
    }

    (heap, clause_table)
}

#[test]
fn test_ordering() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses(&heap);
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
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses(&heap);
    clause_table.find_flags();
    assert_eq!(clause_table.type_flags, [0, 2, 4, 6])
}

#[test]
fn iter_clause_body() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses(&heap);
    clause_table.find_flags();
    let expected = vec!["d(X,Y)".to_string(), "c(X,Y)".to_string(), "b(X,Y)".to_string(), "a(X,Y)".to_string()];
    for i in clause_table.iter(&[ClauseType::CLAUSE, ClauseType::BODY]) {
        assert!(expected.contains(&heap.term_string(clause_table[i][0])));
    }
}

#[test]
fn iter_body_meta_hypothesis() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses(&heap);
    clause_table.find_flags();
    let expected = vec!["g(X,Y)".to_string(),"f(X,Y)".to_string(),"e(X,Y)".to_string(),"d(X,Y)".to_string(), "c(X,Y)".to_string()];
    for i in clause_table.iter(&[ClauseType::BODY, ClauseType::HO, ClauseType::HYPOTHESIS]) {
        assert!(expected.contains(&heap.term_string(clause_table[i][0])));
    }
}

#[test]
fn iter_meta_hypothesis() {
    let (heap, mut clause_table) = setup();
    clause_table.sort_clauses(&heap);
    clause_table.find_flags();
    let expected = vec!["g(X,Y)".to_string(),"f(X,Y)".to_string(),"e(X,Y)".to_string()];
    for i in clause_table.iter(&[ClauseType::HO, ClauseType::HYPOTHESIS]) {
        assert!(expected.contains(&heap.term_string(clause_table[i][0])));
    }
}

#[test]
fn predicate_map(){
    let (mut heap, mut clause_table) = setup();

    //add 2 p/2 clauses

    for clause_string in ["p(a,b)", "p(X,Y)"] {
        let mut clause = Clause::parse_clause(parse_literals(&tokenise(&clause_string)).unwrap(), &mut heap);
        clause_table.add_clause(clause)
    }

    clause_table.sort_clauses(&heap);
    clause_table.find_flags();
    let predicate_map = clause_table.predicate_map(&heap);

    //check predicate map keys are a/2, c/2, d/2, b/2
    for (symbol, arity, clause_count) in [("a", 2, 1),("b", 2, 1),("c", 2, 1),("d", 2, 1),("p", 2, 2),]{
        let symbol = heap.add_const_symbol(symbol);

        let clauses = predicate_map.get(&(symbol, arity)).unwrap();

        assert_eq!(clauses.len(), clause_count)
    }
}

#[test]
fn complex_ordering(){
    let mut heap = Heap::new(200);
    let mut clause_table = ClauseTable::new();

    let clauses = [
        (ClauseType::HO, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::HYPOTHESIS, "g(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::HO, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
        (ClauseType::CLAUSE, "a(a,b,c)"),
        (ClauseType::CLAUSE, "a(a,Z)"),
    ];

    for (clause_type, clause_string) in clauses {
        let mut clause = Clause::parse_clause(parse_literals(&tokenise(&clause_string)).unwrap(), &mut heap);
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