use std::ops::Deref;

use super::clause::Clause;

pub struct Hypothesis (
    Vec<Clause>
);

impl Hypothesis {
    pub fn new() -> Self{
        Hypothesis(Vec::new())
    }

    pub fn len(&self) -> usize{
        self.0.len()
    }

    pub fn push_clause(&mut self, clause: Clause){
        self.0.push(clause);
    }

    pub fn drop_clause(&mut self){
        self.0.pop().unwrap().drop();
    }
}

impl Deref for Hypothesis {
    type Target = Vec<Clause>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}