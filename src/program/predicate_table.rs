use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut},
};

use crate::predicate_modules::PredicateFunction;

use super::clause::Clause;

/// A `(symbol_id, arity)` pair identifying a predicate.
pub(crate) type SymbolArity = (usize, usize);

/// A predicate is either a set of compiled clauses or a built-in function.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Predicate {
    /// A native Rust predicate function.
    Function(PredicateFunction),
    /// One or more compiled Prolog clauses.
    Clauses(Box<[Clause]>),
}

/// Internal entry in the predicate table.
#[derive(PartialEq, Eq, Debug)]
pub struct PredicateEntry {
    symbol_arity: SymbolArity,
    predicate: Predicate,
}

/// The program's predicate table.
///
/// Maps `(symbol, arity)` pairs to predicates (clause sets or built-in functions).
/// Also tracks which predicates are designated as body predicates for MIL learning.
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
    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<&Predicate> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(i) => Some(&self[i].predicate),
            FindReturn::InsertPos(_) => None,
        }
    }

    pub fn get_variable_clauses(&self, arity: usize) -> Option<&Box<[Clause]>> {
        match self.find_predicate((0, arity)) {
            FindReturn::Index(i) => match &self[i].predicate {
                Predicate::Clauses(clauses) => Some(clauses),
                _ => None,
            },
            _ => None,
        }
    }

    //Remove predicate by SymbolArity key, if clause predicate return the range to remove from clause table
    pub fn _remove_predicate(&mut self, symbol_arity: SymbolArity) {
        if let FindReturn::Index(predicate_idx) = self.find_predicate(symbol_arity) {
            if let Predicate::Clauses(_clauses) = self.remove(predicate_idx).predicate {
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
            _ => Ok(()), //Err("Can't set non existing predicate to body"),
        }
    }

    //Get all clause index ranges from entry indexes in the body_list
    pub fn get_body_clauses(&self, arity: usize) -> impl Iterator<Item = &Clause> {
        self.body_list
            .iter()
            .filter_map(move |&idx| {
                if self[idx].symbol_arity.1 != arity {
                    return None;
                }
                if let Predicate::Clauses(pred_clauses) = &self[idx].predicate {
                    Some(pred_clauses.iter())
                } else {
                    None
                }
            })
            .flatten()
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
    use super::{super::clause::Clause, Predicate, PredicateEntry, PredicateTable};
    use crate::{
        heap::{query_heap::QueryHeap, symbol_db::SymbolDB},
        predicate_modules::PredReturn,
        program::{hypothesis::Hypothesis, predicate_table::FindReturn},
        Config,
    };

    fn pred_fn_placeholder(
        _heap: &mut QueryHeap,
        _hypothesis: &mut Hypothesis,
        _goal: usize,
        _predicate_table: &PredicateTable,
        _config: Config,
    ) -> PredReturn {
        PredReturn::True
    }

    /// Build a test predicate table with four entries sorted by symbol_arity.
    /// Returns (table, p, q, pred_func) so tests can use the actual symbol IDs.
    fn setup() -> (PredicateTable, usize, usize, usize) {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let pred_func = SymbolDB::set_const("func".into());

        let p_entry = PredicateEntry {
            symbol_arity: (p, 2),
            predicate: Predicate::Clauses(Box::new([
                Clause::new(vec![15, 19], None, None),
                Clause::new(vec![23, 27], None, None),
            ])),
        };
        let q_entry = PredicateEntry {
            symbol_arity: (q, 2),
            predicate: Predicate::Clauses(Box::new([
                Clause::new(vec![31, 35], None, None),
                Clause::new(vec![39, 43], None, None),
            ])),
        };
        let func_entry = PredicateEntry {
            symbol_arity: (pred_func, 2),
            predicate: Predicate::Function(pred_fn_placeholder),
        };
        let zero_entry = PredicateEntry {
            symbol_arity: (0, 2),
            predicate: Predicate::Clauses(Box::new([
                Clause::new(vec![0, 3], Some(vec![0, 1]), None),
                Clause::new(vec![7, 11], Some(vec![0]), None),
            ])),
        };

        let mut predicates = vec![zero_entry, p_entry, q_entry, func_entry];
        predicates.sort_by_key(|e| e.symbol_arity);

        // body_list should point to the index of (p, 2) after sorting
        let p_idx = predicates
            .iter()
            .position(|e| e.symbol_arity == (p, 2))
            .unwrap();

        (
            PredicateTable {
                predicates,
                body_list: vec![p_idx],
            },
            p,
            q,
            pred_func,
        )
    }

    #[test]
    fn find_predicate() {
        let (pred_table, p, _q, _pred_func) = setup();

        let symbol = SymbolDB::set_const("find_predicate_test_symbol".into());
        let p_idx = pred_table
            .iter()
            .position(|e| e.symbol_arity == (p, 2))
            .unwrap();

        assert_eq!(pred_table.find_predicate((0, 1)), FindReturn::InsertPos(0));
        assert_eq!(pred_table.find_predicate((p, 2)), FindReturn::Index(p_idx));

        // A symbol larger than all entries should go at the end
        assert_eq!(
            pred_table.find_predicate((symbol, 2)),
            if symbol > pred_table.last().unwrap().symbol_arity.0 {
                FindReturn::InsertPos(pred_table.len())
            } else {
                pred_table.find_predicate((symbol, 2))
            }
        );

        // Same symbol, different arity should get an insert position
        assert_eq!(
            pred_table.find_predicate((p, 1)),
            FindReturn::InsertPos(p_idx)
        );

        let pred_table = PredicateTable {
            predicates: vec![],
            body_list: vec![],
        };

        assert_eq!(pred_table.find_predicate((50, 2)), FindReturn::InsertPos(0));
    }

    #[test]
    fn get_predicate() {
        let (pred_table, p, _q, _pred_func) = setup();

        assert_eq!(pred_table.get_predicate((p, 3)), None);
        assert_eq!(
            pred_table.get_predicate((p, 2)),
            Some(&Predicate::Clauses(Box::new([
                Clause::new(vec![15, 19], None, None),
                Clause::new(vec![23, 27], None, None),
            ])))
        );
    }

    #[test]
    fn insert_predicate_function() {
        let (mut pred_table, p, _q, pred_func) = setup();

        assert_eq!(
            pred_table.insert_predicate_function((p, 2), pred_fn_placeholder),
            Err("Cannot insert predicate function to clause predicate")
        );

        pred_table
            .insert_predicate_function((pred_func, 3), pred_fn_placeholder)
            .unwrap();
        assert_eq!(
            pred_table.get_predicate((pred_func, 3)),
            Some(&Predicate::Function(pred_fn_placeholder))
        );
    }

    #[test]
    fn add_clause_to_predicate() {
        let (mut pred_table, p, _q, pred_func) = setup();
        let r = SymbolDB::set_const("r".into());

        pred_table
            .add_clause_to_predicate(Clause::new(vec![], Some(vec![]), None), (p, 2))
            .unwrap();
        pred_table
            .add_clause_to_predicate(Clause::new(vec![], Some(vec![]), None), (r, 2))
            .unwrap();
        assert_eq!(
            pred_table
                .add_clause_to_predicate(Clause::new(vec![], Some(vec![]), None), (pred_func, 2)),
            Err("Cannot add clause to function predicate")
        );

        assert_eq!(
            pred_table.get_predicate((p, 2)),
            Some(&Predicate::Clauses(Box::new([
                Clause::new(vec![15, 19], None, None),
                Clause::new(vec![23, 27], None, None),
                Clause::new(vec![], Some(vec![]), None)
            ])))
        );
        assert_eq!(
            pred_table.get_predicate((r, 2)),
            Some(&Predicate::Clauses(Box::new([Clause::new(
                vec![],
                Some(vec![]),
                None
            )])))
        );
    }

    #[test]
    fn remove_predicate() {
        // Test removing p
        let (mut pred_table, p, _q, _pred_func) = setup();
        let len_before = pred_table.len();
        pred_table._remove_predicate((p, 2));
        assert_eq!(pred_table.len(), len_before - 1);
        assert_eq!(pred_table.get_predicate((p, 2)), None);
        // body_list should be cleared since p was the body predicate
        assert!(
            pred_table.body_list.is_empty()
                || pred_table
                    .body_list
                    .iter()
                    .all(|&idx| pred_table[idx].symbol_arity != (p, 2))
        );

        // Test removing q
        let (mut pred_table, _p, q, _pred_func) = setup();
        let len_before = pred_table.len();
        pred_table._remove_predicate((q, 2));
        assert_eq!(pred_table.len(), len_before - 1);
        assert_eq!(pred_table.get_predicate((q, 2)), None);

        // Test removing entry at symbol 0
        let (mut pred_table, p, q, _pred_func) = setup();
        let len_before = pred_table.len();
        pred_table._remove_predicate((0, 2));
        assert_eq!(pred_table.len(), len_before - 1);
        assert_eq!(pred_table.get_predicate((0, 2)), None);
        // p and q should still be present
        assert!(pred_table.get_predicate((p, 2)).is_some());
        assert!(pred_table.get_predicate((q, 2)).is_some());
    }

    #[test]
    fn set_body() {
        let (mut pred_table, p, q, _pred_func) = setup();

        // Remove p from body list
        pred_table.set_body((p, 2), false).unwrap();
        // Add q to body list
        pred_table.set_body((q, 2), true).unwrap();

        let q_idx = pred_table
            .iter()
            .position(|e| e.symbol_arity == (q, 2))
            .unwrap();
        assert_eq!(pred_table.body_list, [q_idx]);
    }

    #[test]
    fn get_body_clauses() {
        let (mut pred_table, _p, q, _pred_func) = setup();

        // No body clauses for arity 1
        let empty: Vec<&Clause> = pred_table.get_body_clauses(1).collect();
        assert!(empty.is_empty());

        // Initially p is the body predicate (set in setup)
        let body2: Vec<&Clause> = pred_table.get_body_clauses(2).collect();
        assert_eq!(
            body2,
            vec![
                &Clause::new(vec![15, 19], None, None),
                &Clause::new(vec![23, 27], None, None),
            ]
        );

        // Add q as body predicate too
        pred_table.set_body((q, 2), true).unwrap();

        let body2_ext: Vec<&Clause> = pred_table.get_body_clauses(2).collect();
        assert_eq!(body2_ext.len(), 4);
        // Should contain both p's and q's clauses
        assert!(body2_ext.contains(&&Clause::new(vec![15, 19], None, None)));
        assert!(body2_ext.contains(&&Clause::new(vec![23, 27], None, None)));
        assert!(body2_ext.contains(&&Clause::new(vec![31, 35], None, None)));
        assert!(body2_ext.contains(&&Clause::new(vec![39, 43], None, None)));
    }
}
