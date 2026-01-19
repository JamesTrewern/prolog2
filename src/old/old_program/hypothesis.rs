use std::usize;

use crate::{
    heap::{
        heap::Heap,
        store::{Store, Tag},
        symbol_db::SymbolDB,
    },
    resolution::unification::Binding,
};

use super::{
    clause::Clause,
    clause_table::{ClauseIterator, ClauseTable},
};

const PRED_NAME: &'static str = "pred";

#[derive(Clone)]
pub struct Hypothesis {
    pub clauses: ClauseTable,
    constraints: Vec<Box<[(usize, usize)]>>,
    pub invented_preds: usize,
}

impl Hypothesis {
    pub fn new() -> Hypothesis {
        Hypothesis {
            clauses: ClauseTable::new(),
            invented_preds: 0,
            constraints: vec![],
        }
    }

    pub fn from_table(clauses: ClauseTable) -> Hypothesis {
        Hypothesis {
            clauses,
            invented_preds: 0,
            constraints: Vec::new(),
        }
    }

    /**Add clause to hypothesis, If invented predicate symbol return Some(new symbol id)*/
    pub fn add_h_clause(&mut self, clause: Clause, heap: &mut Store) -> Option<usize> {
        //Build contraints for new clause. This assumes that no unifcation should happen between variable predicate symbols
        let mut constraints = Vec::<(usize, usize)>::new();
        for i in 0..clause.len() {
            for j in i..clause.len() {
                match (heap[clause[i] + 1], heap[clause[j] + 1]) {
                    ((Tag::Ref, addr1), (Tag::Ref, addr2)) if addr1 != addr2 => {
                        constraints.push((clause[i] + 1, clause[j] + 1));
                        constraints.push((clause[j] + 1, clause[i] + 1));
                    }
                    ((Tag::Ref, addr1), (Tag::Con, addr2)) if addr1 != addr2 => {
                        constraints.push((clause[i] + 1, clause[j] + 1))
                    }
                    ((Tag::Con, addr1), (Tag::Ref, addr2)) if addr1 != addr2 => {
                        constraints.push((clause[j] + 1, clause[i] + 1))
                    }
                    _ => (),
                }
            }
        }
        self.constraints.push(constraints.into());

        //Get clause symbol before ownership is moved to clause table
        let (mut symbol, _) = clause.symbol_arity(heap);

        //Add clause to clause table and icrement H clause counter
        self.clauses.add_clause(clause);

        //If head predicate is variable invent new symbol
        if symbol < Store::CON_PTR {
            self.invented_preds += 1;
            symbol = SymbolDB::set_const(&format!("{PRED_NAME}_{}", self.invented_preds));
            Some(heap.set_const(symbol))
        } else {
            None
        }
    }

    /**Remove clause from hypothesis */
    pub fn remove_h_clause(&mut self, invented: bool, debug: bool) {
        if invented {
            self.invented_preds -= 1;
        }
        if debug {
            println!("Removed Clause");
        }
        self.clauses.remove_clause(self.clauses.len() - 1);

        self.constraints.pop();
    }

    /**Check if binding will unify variable predicate symbols inside a H clause */
    pub fn check_constraints(&self, binding: &Binding, heap: &Store) -> bool {
        for cons in self.constraints.iter() {
            for con in cons.iter() {
                let constraint = (heap.deref_addr(con.0), heap.deref_addr(con.1));
                if let Some(bound) = binding.bound(constraint.0) {
                    if heap[constraint.1] == heap[bound] {
                        return true;
                    }
                }
            }
        }
        false
    }

    /** Create symbols for all variables in the hypothesis*/
    pub fn normalise_hypothesis(&self, heap: &mut Store) {
        //TO DO could turn unbound refs in H into constants
        for i in 0..self.clauses.len() {
            self.clauses.get(i).normalise(heap);
        }
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn iter(&self) -> ClauseIterator {
        self.clauses.iter()
    }

    pub fn get(&self, index: usize) -> Clause {
        self.clauses.get(index)
    }
}
