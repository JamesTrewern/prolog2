use crate::{clause::*, solver::Proof, State};

#[test]
fn body_pred() {
    let mut state = State::new(None);
    state.heap.query_space = false;
    for clause in ["dad(adam,james)", "mum(tami,james)"] {
        let (clause_type, clause) = Clause::parse_clause(clause, &mut state.heap);
        state.prog.add_clause(clause_type, clause)
    }
    state.heap.query_space = true;
    let directive = state.parse_goals("body_pred(dad,2),body_pred(mum,2)");
    assert!(Proof::new(&directive, &mut state).next().is_some());
    let body_clauses: Vec<String> = state
        .prog
        .clauses
        .iter(&[ClauseType::BODY])
        .map(|c| c.1 .1.to_string(&state.heap))
        .collect();
    assert_eq!(&body_clauses,&["mum(tami,james)", "dad(adam,james)"])
}
