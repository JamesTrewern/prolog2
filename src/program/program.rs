use crate::heap::heap::Heap;

use super::{
    clause_table::{Clause, ClauseTable},
    predicate_table::{PredicateFN, PredicateTable, SymbolArity},
};

pub enum CallResult {
    Clauses(Vec<Clause>),
    Function(PredicateFN),
}

pub struct Program {
    clause_table: ClauseTable,
    predicate_table: PredicateTable,
}

impl Program {
    pub fn new() -> Self {
        Program {
            clause_table: ClauseTable::new(),
            predicate_table: PredicateTable::new(),
        }
    }

    pub fn add_pred_function(
        &mut self,
        symbol_arity: SymbolArity,
        predicate_fn: PredicateFN,
    ) -> Result<(), &str> {
        self.predicate_table
            .insert_predicate_function(symbol_arity, predicate_fn)
    }

    pub fn add_clause(&mut self, clause: Clause, heap: &impl Heap) -> Result<(), &str> {
        let symbol_arity = heap.str_symbol_arity(clause.head());
        let clause_idx = self.clause_table.insert(clause, heap);
        self.predicate_table
            .add_clause_to_predicate(clause_idx, symbol_arity)
    }

    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) {
        if let Some(range) = self.predicate_table.remove_predicate(symbol_arity) {
            self.clause_table.remove_clauses(range.0..range.1);
        }
    }

    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<CallResult> {
        match self.predicate_table.get_predicate(symbol_arity) {
            Some(predicate) => match predicate.predicate {
                super::predicate_table::PredClFn::Function(predicate_fn) => {
                    Some(CallResult::Function(predicate_fn))
                }
                super::predicate_table::PredClFn::Clauses(range) => {
                    let mut clauses: Vec<Clause> = (range.0..range.1)
                        .into_iter()
                        .map(|idx| self.clause_table.get(idx).unwrap())
                        .collect();
                    if symbol_arity.0 == 0 {
                        clauses.append(&mut self.get_body(symbol_arity.1));
                    }
                    Some(CallResult::Clauses(clauses))
                }
            },
            None => None,
        }
    }

    pub fn get_body(&self, arity: usize) -> Vec<Clause> {
        let ranges = self.predicate_table.get_body_clauses(arity);
        let mut body_clauses = Vec::<Clause>::new();

        for range in ranges {
            for i in range.0..range.1 {
                body_clauses.push(self.clause_table.get(i).unwrap());
            }
        }

        body_clauses
    }
}
