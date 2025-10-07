use std::{ops::{Deref, DerefMut}, sync::Arc};

use crate::{heap::heap::Heap, program::predicate_table::SymbolArity};

use super::clause::Clause;

pub type Constraints = Arc<[(usize,usize)]>;

pub struct Hypothesis (Vec<(Clause,Constraints)>);
    

impl Hypothesis {
    pub fn new() -> Self {
        Hypothesis(Vec::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn push_clause(&mut self, clause: Clause, heap: &impl Heap, constraints: Constraints) {
        self.0.push((clause,constraints));
    }

    pub fn to_string(&self, heap: &impl Heap) -> String{
        let mut buffer = String::new();
        for (clause,_) in &self.0 {
            buffer += &clause.to_string(heap);
            buffer += "\n"
        }
        buffer
    }
}

impl Deref for Hypothesis {
    type Target = Vec<(Clause,Constraints)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Hypothesis{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
