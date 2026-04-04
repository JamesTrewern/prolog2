use std::{ops::{Deref, DerefMut}, sync::atomic::{AtomicUsize, Ordering::Relaxed}};

use smallvec::SmallVec;

use crate::heap::heap::Heap;

use super::clause::Clause;

/// Constraint set for existentially quantified variables in a learned clause.
pub type Constraints = SmallVec<[usize; 5]>;

static PRED_N: AtomicUsize = AtomicUsize::new(0);

/// A collection of learned clauses produced during proof search.
///
/// During MIL resolution, when a second-order clause matches a goal,
/// a new first-order clause is invented and added to the hypothesis.
#[derive(Clone)]
pub struct Hypothesis {
    clauses: Vec<Clause>,
    pub constraints: Vec<Constraints>,
}

impl Hypothesis {
    pub fn new() -> Self {
        Hypothesis {
            clauses: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn push_clause(&mut self, clause: Clause, constraints: Constraints) {
        self.clauses.push(clause);
        self.constraints.push(constraints);
    }

    pub fn pop_clause(&mut self) -> Clause {
        self.constraints.pop();
        self.clauses.pop().unwrap()
    }

    pub fn to_string(&self, heap: &impl Heap) -> String {
        let mut buffer = String::new();
        for clause in &self.clauses {
            buffer += &clause.to_string(heap);
            buffer += "\n"
        }
        buffer
    }

    pub fn next_pred_id() -> usize{
        PRED_N.fetch_add(1, Relaxed)
    }
}

impl Deref for Hypothesis {
    type Target = Vec<Clause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for Hypothesis {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}
