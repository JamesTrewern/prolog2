use super::clause::Clause;

pub struct Hypothesis {
    clauses: Vec<Clause>,
    n_inv_predicate: u8,
}