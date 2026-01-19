use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use crate::{heap::heap::Heap, program::predicate_table::SymbolArity};

use super::clause::Clause;

pub type Constraints = Arc<[usize]>;

pub struct Hypothesis {
    clauses: Vec<Clause>,
    pub constraints: Vec<Constraints>,
}

impl Hypothesis {
    pub fn new() -> Self {
        Hypothesis{clauses: Vec::new(), constraints: Vec::new()}
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn push_clause(&mut self, clause: Clause, heap: &impl Heap, constraints: Constraints) {
        self.clauses.push(clause);
        self.constraints.push(constraints);
    }

    pub fn pop_clause(&mut self){
        self.clauses.pop();
        self.constraints.pop();
    }

    pub fn to_string(&self, heap: &impl Heap) -> String {
        let mut buffer = String::new();
        for clause in &self.clauses {
            buffer += &clause.to_string(heap);
            buffer += "\n"
        }
        buffer
    }
}

impl Deref for Hypothesis {
    type Target = Vec<Clause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for Hypothesis{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}
