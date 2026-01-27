use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
};

use crate::predicate_modules::PredicateFunction;

use super::clause::Clause;

// use bumpalo::{Bump};self.choices = hypothesis.get_predicate((symbol, arity))
pub(crate) type SymbolArity = (usize, usize);

/* A predicate takes the form of a range of indexes in the clause table,
or a function which uses rust code to evaluate to a truth value and/or return bindings*/
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Predicate {
    Function(PredicateFunction),
    Clauses(Box<[Clause]>),
}

#[derive(PartialEq, Eq, Debug)]
pub struct PredicateEntry {
    symbol_arity: SymbolArity,
    predicate: Predicate,
}

#[derive(Debug, PartialEq)]
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
        let mut ub: usize = self.len();
        let mut mid: usize;

        while ub > lb {
            mid = (lb + ub) / 2;
            match symbol_arity.cmp(&self[mid].symbol_arity) {
                Ordering::Less => ub = mid,
                Ordering::Equal => return FindReturn::Index(mid),
                Ordering::Greater => lb = mid + 1,
            }
        }
        FindReturn::InsertPos(lb)
    }

    //Inserts a new predicate function to the table
    pub fn insert_predicate_function(
        &mut self,
        symbol_arity: SymbolArity,
        predicate_fn: PredicateFunction,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self[idx].predicate {
                Predicate::Function(old_predicate_fn) => {
                    *old_predicate_fn = predicate_fn;
                    Ok(())
                }
                _ => Err("Cannot insert predicate function to clause predicate"),
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
    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<Predicate> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(i) => match &self[i].predicate {
                Predicate::Function(predicate_fn) => Some(Predicate::Function(*predicate_fn)),
                Predicate::Clauses(clauses) => Some(Predicate::Clauses(clauses.clone())),
            },
            FindReturn::InsertPos(_) => None,
        }
    }

    pub fn get_variable_clauses(&self, arity: usize) -> Option<&Box<[Clause]>>{
        match self.find_predicate((0,arity)) {
            FindReturn::Index(i) => match &self[i].predicate {
                Predicate::Clauses(clauses) => Some(clauses),
                _ => None
            },
            _ => None,
        }
    }

    //Remove predicate by SymbolArity key, if clause predicate return the range to remove from clause table
    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) {
        if let FindReturn::Index(predicate_idx) = self.find_predicate(symbol_arity) {
            if let Predicate::Clauses(clauses) = self.remove(predicate_idx).predicate {
                self.body_list.retain(|i| *i != predicate_idx);
            }
            for i in &mut self.body_list {
                if *i > predicate_idx {
                    println!("{i}");
                    *i -= 1;
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use crate::{
        heap::{query_heap::QueryHeap, symbol_db::SymbolDB},
        predicate_modules::{PredReturn,PredicateFunction},
        program::{hypothesis::Hypothesis, predicate_table::FindReturn},
        Config,
    };

    use super::{super::clause::Clause, Predicate, PredicateEntry, PredicateTable};

    fn pred_fn_placeholder(
        _heap: &mut QueryHeap,
        _hypothesis: &mut Hypothesis,
        _goal: usize,
        _predicate_table: Arc<PredicateTable>,
        _config: Config,
    ) -> PredReturn {
        PredReturn::True
    }

    fn setup() -> PredicateTable {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let pred_func = SymbolDB::set_const("func".into());

        if q < p || q > pred_func {
            panic!("q comes before p in predicate table tests");
        }

        PredicateTable {
            predicates: vec![
                PredicateEntry {
                    symbol_arity: (0, 2),
                    predicate: Predicate::Clauses(Box::new([
                        Clause::new(vec![0, 3], Some(vec![0, 1])),
                        Clause::new(vec![7, 11], Some(vec![0])),
                    ])),
                },
                PredicateEntry {
                    symbol_arity: (p, 2),
                    predicate: Predicate::Clauses(Box::new([
                        Clause::new(vec![15, 19], None),
                        Clause::new(vec![23, 27], None),
                    ])),
                },
                PredicateEntry {
                    symbol_arity: (q, 2),
                    predicate: Predicate::Clauses(Box::new([
                        Clause::new(vec![31, 35], None),
                        Clause::new(vec![39, 43], None),
                    ])),
                },
                PredicateEntry {
                    symbol_arity: (pred_func, 2),
                    predicate: Predicate::Function(pred_fn_placeholder),
                },
            ],
            body_list: vec![1],
        }
    }

    #[test]
    fn find_predicate() {
        let pred_table = setup();

        let symbol = SymbolDB::set_const("find_predicate_test_symbol".into());
        let p = SymbolDB::set_const("p".into());

        assert_eq!(pred_table.find_predicate((0, 1)), FindReturn::InsertPos(0));
        assert_eq!(
            pred_table.find_predicate((symbol, 2)),
            FindReturn::InsertPos(4)
        );
        assert_eq!(pred_table.find_predicate((p, 1)), FindReturn::InsertPos(1));
        assert_eq!(pred_table.find_predicate((p, 2)), FindReturn::Index(1));

        let pred_table = PredicateTable{
            predicates: vec![],
            body_list: vec![],
        };

        assert_eq!(pred_table.find_predicate((50,2)), FindReturn::InsertPos(0));
    }

    #[test]
    fn get_predicate() {
        let pred_table = setup();
        let p = SymbolDB::set_const("p".into());

        assert_eq!(pred_table.get_predicate((p, 3)), None);
        assert_eq!(
            pred_table.get_predicate((p, 2)),
            Some(Predicate::Clauses(Box::new([
                Clause::new(vec![15, 19], None),
                Clause::new(vec![23, 27], None),
            ])))
        );
    }

    #[test]
    fn insert_predicate_function() {
        let mut pred_table = setup();
        let pred_func = SymbolDB::set_const("func".into());
        let p = SymbolDB::set_const("p".into());

        assert_eq!(
            pred_table.insert_predicate_function((p, 2), pred_fn_placeholder),
            Err("Cannot insert predicate function to clause predicate")
        );

        pred_table
            .insert_predicate_function((pred_func, 3), pred_fn_placeholder)
            .unwrap();
        assert_eq!(
            pred_table.get_predicate((pred_func, 3)),
            Some(Predicate::Function(pred_fn_placeholder))
        );
    }

    #[test]
    fn add_clause_to_predicate() {
        let mut pred_table = setup();
        let p = SymbolDB::set_const("p".into());
        let r = SymbolDB::set_const("r".into());
        let pred_func = SymbolDB::set_const("func".into());

        pred_table
            .add_clause_to_predicate(Clause::new(vec![], Some(vec![])), (p, 2))
            .unwrap();
        pred_table
            .add_clause_to_predicate(Clause::new(vec![], Some(vec![])), (r, 2))
            .unwrap();
        assert_eq!(
            pred_table.add_clause_to_predicate(Clause::new(vec![], Some(vec![])), (pred_func, 2)),
            Err("Cannot add clause to function predicate")
        );

        assert_eq!(
            pred_table.get_predicate((p, 2)),
            Some(Predicate::Clauses(Box::new([
                Clause::new(vec![15, 19], None),
                Clause::new(vec![23, 27], None),
                Clause::new(vec![], Some(vec![]))
            ])))
        );
        assert_eq!(
            pred_table.get_predicate((r, 2)),
            Some(Predicate::Clauses(Box::new([Clause::new(
                vec![],
                Some(vec![])
            )])))
        );
    }

    #[test]
    fn remove_predicate() {
        let mut pred_table = setup();
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let pred_func = SymbolDB::set_const("func".into());

        pred_table.remove_predicate((p, 2));

        assert_eq!(
            pred_table,
            PredicateTable {
                predicates: vec![
                    PredicateEntry {
                        symbol_arity: (0, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![0, 3], Some(vec![0, 1])),
                            Clause::new(vec![7, 11], Some(vec![0])),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (q, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![31, 35], None),
                            Clause::new(vec![39, 43], None),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (pred_func, 2),
                        predicate: Predicate::Function(pred_fn_placeholder),
                    },
                ],
                body_list: vec![],
            }
        );

        let mut pred_table = setup();
        pred_table.remove_predicate((q, 2));

        assert_eq!(
            pred_table,
            PredicateTable {
                predicates: vec![
                    PredicateEntry {
                        symbol_arity: (0, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![0, 3], Some(vec![0, 1])),
                            Clause::new(vec![7, 11], Some(vec![0])),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (p, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![15, 19], None),
                            Clause::new(vec![23, 27], None),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (pred_func, 2),
                        predicate: Predicate::Function(pred_fn_placeholder),
                    },
                ],
                body_list: vec![1],
            }
        );

        let mut pred_table = setup();
        pred_table.remove_predicate((0, 2));

        assert_eq!(
            pred_table,
            PredicateTable {
                predicates: vec![
                    PredicateEntry {
                        symbol_arity: (p, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![15, 19], None),
                            Clause::new(vec![23, 27], None),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (q, 2),
                        predicate: Predicate::Clauses(Box::new([
                            Clause::new(vec![31, 35], None),
                            Clause::new(vec![39, 43], None),
                        ])),
                    },
                    PredicateEntry {
                        symbol_arity: (pred_func, 2),
                        predicate: Predicate::Function(pred_fn_placeholder),
                    },
                ],
                body_list: vec![0],
            }
        );
    }

    #[test]
    fn set_body() {
        let mut pred_table = setup();
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let pred_func = SymbolDB::set_const("func".into());

        pred_table.set_body((p, 2), false).unwrap();
        pred_table.set_body((q, 2), true).unwrap();
        assert_eq!(
            pred_table.set_body((pred_func, 2), true),
            Err("Can't set predicate function to body")
        );
        assert_eq!(
            pred_table.set_body((100, 2), true),
            Err("Can't set non existing predicate to body")
        );

        assert_eq!(pred_table.body_list, [2]);
    }

    #[test]
    fn get_body_clauses() {
        let mut pred_table = setup();
        let q = SymbolDB::set_const("q".into());

        assert_eq!(pred_table.get_body_clauses(1), []);
        assert_eq!(
            pred_table.get_body_clauses(2),
            [
                Clause::new(vec![15, 19], None),
                Clause::new(vec![23, 27], None),
            ]
        );

        pred_table.set_body((q, 2), true).unwrap();

        assert_eq!(
            pred_table.get_body_clauses(2),
            [
                Clause::new(vec![15, 19], None),
                Clause::new(vec![23, 27], None),
                Clause::new(vec![31, 35], None),
                Clause::new(vec![39, 43], None),
            ]
        );
    }
}
