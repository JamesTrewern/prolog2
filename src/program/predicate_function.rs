use crate::{heap::{heap::Heap, query_heap::QueryHeap}, program::hypothesis::Hypothesis, resolution::{proof::Proof, unification::Substitution}};

pub enum PredReturn {
    True,
    False,
    Binding(Vec<(usize,usize)>),
}

impl PredReturn {
    pub fn bool(value: bool) -> PredReturn {
        if value {
            PredReturn::True
        } else {
            PredReturn::False
        }
    }
}

//Take Proof and pointer to function call term and return true(possibly with binding), or false
pub type PredicateFunction = fn(&mut QueryHeap, &mut Hypothesis, usize) -> PredReturn;