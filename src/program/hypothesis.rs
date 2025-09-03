use std::ops::Deref;

use crate::{heap::heap::Heap, program::predicate_table::SymbolArity};

use super::clause::Clause;

pub struct Hypothesis(Vec<(SymbolArity, Clause)>);

impl Hypothesis {
    pub fn new() -> Self {
        Hypothesis(Vec::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn push_clause(&mut self, clause: Clause, heap: &impl Heap) {
        self.0.push((heap.str_symbol_arity(clause.head()), clause));
    }

    pub fn drop_clause(&mut self) {
        self.0.pop().unwrap().1.drop();
    }

    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Vec<Clause> {
        if symbol_arity.0 == 0 {
            self.0
                .iter()
                .filter_map(|((_, arity), clause)| {
                    if *arity == symbol_arity.1 {
                        Some(*clause)
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.0
                .iter()
                .filter_map(|(clause_symbol_arity, clause)| {
                    if *clause_symbol_arity == symbol_arity {
                        Some(*clause)
                    } else {
                        None
                    }
                })
                .collect()
        }
    }
}

// impl Deref for Hypothesis {
//     type Target = Vec<Clause>;

//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }
