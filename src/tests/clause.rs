use crate::{clause::*, Heap};

#[test]
fn parse_fact(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(x,y)", &mut heap);
    assert_eq!(clause_type, ClauseType::CLAUSE);
    assert_eq!(heap.term_string(clause[0]), "p(x,y)");
}

#[test]
fn parse_meta_fact_1(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("P(x,y)", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "P(x,y)");
}

#[test]
fn parse_meta_fact_2(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y)\\X,Y", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "p(∀'X,∀'Y)");
}

#[test]
#[should_panic]
fn parse_faulty_fact(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(x,q(Y)", &mut heap);
}

#[test]
fn parse_clause(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y):-q(X),r(Y)", &mut heap);
    assert_eq!(clause_type, ClauseType::CLAUSE);
    assert_eq!(heap.term_string(clause[0]), "p(X,Y)");
    assert_eq!(heap.term_string(clause[1]), "q(X)");
    assert_eq!(heap.term_string(clause[2]), "r(Y)");
}

#[test]
fn parse_clause_with_con(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y,z):-q(X),r(Y)", &mut heap);
    assert_eq!(clause_type, ClauseType::CLAUSE);
    assert_eq!(heap.term_string(clause[0]), "p(X,Y,z)");
    assert_eq!(heap.term_string(clause[1]), "q(X)");
    assert_eq!(heap.term_string(clause[2]), "r(Y)");
}
#[test]
fn parse_clause_with_list(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p([X,Y,z]):-q(X,Y)", &mut heap);
    assert_eq!(clause_type, ClauseType::CLAUSE);
    assert_eq!(heap.term_string(clause[0]), "p([X,Y,z])");
    assert_eq!(heap.term_string(clause[1]), "q(X,Y)");
}

#[test]
#[should_panic]
fn parse_faulty_clause_1(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p([X,Y,z):-q(X),r(Y)", &mut heap);
}

#[test]
#[should_panic]
fn parse_faulty_clause_2(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y,z):-q(X,r(Y)", &mut heap);
}

#[test]
fn parse_meta_clause_with_con(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("P(X,Y,z):-Q(X),R(Y)\\X,Y", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "P(∀'X,∀'Y,z)");
    assert_eq!(heap.term_string(clause[1]), "Q(∀'X)");
    assert_eq!(heap.term_string(clause[2]), "R(∀'Y)");
}

#[test]
fn parse_meta_clause_with_list(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("P([X,Y]):-Q(X),R(Y)\\X,Y", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "P([∀'X,∀'Y])");
    assert_eq!(heap.term_string(clause[1]), "Q(∀'X)");
    assert_eq!(heap.term_string(clause[2]), "R(∀'Y)");
}

#[test]
fn parse_meta_clause_no_uni_vars(){
    let mut heap = Heap::new(20);
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("P(X,Y):-Q(X),R(Y)", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "P(X,Y)");
    assert_eq!(heap.term_string(clause[1]), "Q(X)");
    assert_eq!(heap.term_string(clause[2]), "R(Y)");
}

#[test]
fn parse_meta_clause_no_var_preds(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y,z):-q(X),r(Y)\\X,Y", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "p(∀'X,∀'Y,z)");
    assert_eq!(heap.term_string(clause[1]), "q(∀'X)");
    assert_eq!(heap.term_string(clause[2]), "r(∀'Y)");
}

#[test]
fn parse_meta_clause_con_head_pred(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y):-Q(X),R(Y)\\X,Y", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "p(∀'X,∀'Y)");
    assert_eq!(heap.term_string(clause[1]), "Q(∀'X)");
    assert_eq!(heap.term_string(clause[2]), "R(∀'Y)");
}

#[test]
fn parse_meta_clause_con_head_pred_no_uni_vars(){
    let mut heap = Heap::new(20);
    let (clause_type, clause) = Clause::parse_clause("p(X,Y):-Q(X),R(Y)", &mut heap);
    assert_eq!(clause_type, ClauseType::META);
    assert_eq!(heap.term_string(clause[0]), "p(X,Y)");
    assert_eq!(heap.term_string(clause[1]), "Q(X)");
    assert_eq!(heap.term_string(clause[2]), "R(Y)");
}