use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
};

use super::clause::Clause;

// use bumpalo::{Bump};

pub(crate) type SymbolArity = (usize, usize);

//TODO create predicate function type
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub struct PredicateFN;

/* A predicate takes the form of a range of indexes in the clause table,
or a function which uses rust code to evaluate to a truth value and/or return bindings*/
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Predicate {
    Function(PredicateFN),
    Clauses(Box<[Clause]>),
}

#[derive(PartialEq, Eq, Debug)]
pub struct PredicateEntry {
    symbol_arity: SymbolArity,
    predicate: Predicate,
}

pub struct PredicateTable {
    predicates: Vec<PredicateEntry>,
    body_list: Vec<usize>,

}

//Return type for binary search of predicate keys
#[derive(Debug, PartialEq, Eq)]
enum FindReturn {
    Index(usize),
    InsertPos(usize),
}

enum CallReturn {
    Clauses(Vec<Clause>),
    Function(PredicateFN)
}

impl PredicateTable {
    pub fn new() -> Self {
        PredicateTable {
            predicates: vec![],
            body_list: vec![],
        }
    }

    //Performs a binary search of the ordered predicate table. 
    fn find_predicate(&self, symbol_arity: SymbolArity) -> FindReturn {
        let mut lb: usize = 0;
        let mut ub: usize = self.len() - 1;
        let mut mid: usize;
        while ub > lb {
            mid = (lb + ub) / 2;
            match symbol_arity.cmp(&self[mid].symbol_arity) {
                Ordering::Less => ub = mid - 1,
                Ordering::Equal => return FindReturn::Index(mid),
                Ordering::Greater => lb = mid + 1,
            }
        }
        match symbol_arity.cmp(&self[lb].symbol_arity) {
            Ordering::Less => FindReturn::InsertPos(lb),
            Ordering::Equal => FindReturn::Index(lb),
            Ordering::Greater => FindReturn::InsertPos(lb + 1),
        }
    }

    //Inserts a new predicate function to the table
    pub fn insert_predicate_function(
        &mut self,
        symbol_arity: SymbolArity,
        predicate_fn: PredicateFN,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self[idx].predicate {
                Predicate::Function(old_predicate_fn) => {
                    *old_predicate_fn = predicate_fn;
                    Ok(())
                }
                _ => Err("Cannot insert predicate function to clause table predicate"),
            },
            FindReturn::InsertPos(insert_idx) => {
                self.insert(
                    insert_idx,
                    PredicateEntry {
                        symbol_arity,
                        predicate: Predicate::Function(predicate_fn),
                    },
                );
                Ok(())
            }
        }
    }

    //Adds a clause to an existing enrty or creates a new entry with a single clause
    pub fn add_clause_to_predicate(
        &mut self,
        clause: Clause,
        symbol_arity: SymbolArity,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self.get_mut(idx).unwrap().predicate {
                Predicate::Function(_) => return Err("Cannot add clause to function predicate"),
                Predicate::Clauses(clauses) => {
                   *clauses = [&**clauses, &[clause]].concat().into_boxed_slice();
                }
            },
            FindReturn::InsertPos(insert_idx) => {
                self.insert(
                    insert_idx,
                    PredicateEntry {
                        symbol_arity,
                        predicate: Predicate::Clauses(Box::new([clause])),
                    },
                );
            }
        };
        Ok(())
    }

    //Get predicate by SymbolArity key
    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<CallReturn> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(i) => match &self[i].predicate {
                Predicate::Function(predicate_fn) => Some(CallReturn::Function(*predicate_fn)),
                Predicate::Clauses(clauses) => todo!(),
            },
            FindReturn::InsertPos(_) => None,
        }
    }

    //Remove predicate by SymbolArity key, if clause predicate return the range to remove from clause table
    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) {
        if let FindReturn::Index(predicate_idx) = self.find_predicate(symbol_arity) {
            if let Predicate::Clauses(clauses) = self.remove(predicate_idx).predicate{
                for clause in clauses{
                    clause.drop();
                }
            }
        }
    }

    //Remove or add entry index from the body predicate list
    pub fn set_body(&mut self, symbol_arity: SymbolArity, value: bool) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => {
                let predicate = &mut self[idx];
                if matches!(predicate.predicate, Predicate::Function(_)) {
                    Err("Can't set predicate function to body")
                } else {
                    if value == false {
                        self.body_list.retain(|&idx2| idx != idx2);
                    } else {
                        self.body_list.push(idx);
                    }
                    Ok(())
                }
            }
            _ => Err("Can't set non existing predicate to body"),
        }
    }

    //Get all clause index ranges from entry indexes in the body_list
    pub fn get_body_clauses(&self, arity: usize) -> Vec<Clause> {
        let mut body_clauses = vec![];

        for &idx in &self.body_list {
            if self[idx].symbol_arity.1 != arity {
                continue;
            }
            if let Predicate::Clauses(pred_clauses) = &self[idx].predicate {
                body_clauses.extend_from_slice(pred_clauses);
            }
        }

        body_clauses
    }
}

impl Deref for PredicateTable {
    type Target = Vec<PredicateEntry>;

    fn deref(&self) -> &Self::Target {
        &self.predicates
    }
}

impl DerefMut for PredicateTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.predicates
    }
}
