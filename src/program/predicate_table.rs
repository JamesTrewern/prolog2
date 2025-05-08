use std::{
    cmp::Ordering,
    ops::{Deref, DerefMut, Range},
};

pub(crate) type SymbolArity = (usize, usize);

//TODO create predicate function type
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub struct PredicateFN;

/* A predicate takes the form of a range of indexes in the clause table,
or a function which uses rust code to evaluate to a truth value and/or return bindings*/
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Predicate {
    Function(PredicateFN),
    Clauses((usize, usize)),
}

#[derive(PartialEq, Eq, Debug)]
pub struct PredicateEntry {
    symbol_arity: SymbolArity,
    predicate: Predicate,
}

impl PredicateEntry {
    /* When clauses are deleted from or added to the clause table,
    this function shifts the start and end of the clause index range by the step,
    if self.predicate is a Predicate::Funtion this is ignored*/
    pub fn shift_clause_range(&mut self, step: isize) {
        if let Predicate::Clauses(range) = &mut self.predicate {
            range.0 = (range.0 as isize + step) as usize;
            range.1 = (range.1 as isize + step) as usize;
        }
    }
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
        clause_idx: usize,
        symbol_arity: SymbolArity,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self.get_mut(idx).unwrap().predicate {
                Predicate::Function(_) => return Err("Cannot add clause to function predicate"),
                Predicate::Clauses(range) => {
                    if range.1 == clause_idx {
                        range.1 += 1;
                        for predicate in &mut self[idx + 1..] {
                            predicate.shift_clause_range(1);
                        }
                    } else {
                        return Err("New clause index was not at end of current range");
                    }
                }
            },
            FindReturn::InsertPos(insert_idx) => {
                self.insert(
                    insert_idx,
                    PredicateEntry {
                        symbol_arity,
                        predicate: Predicate::Clauses((clause_idx, clause_idx + 1)),
                    },
                );
                for predicate in &mut self[insert_idx + 1..] {
                    predicate.shift_clause_range(1);
                }
            }
        };
        Ok(())
    }

    //Get predicate by SymbolArity key
    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<Predicate> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(i) => Some(self[i].predicate),
            FindReturn::InsertPos(_) => None,
        }
    }

    //Remove predicate by SymbolArity key, if clause predicate return the range to remove from clause table
    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) -> Option<(usize, usize)> {
        if let FindReturn::Index(predicate_idx) = self.find_predicate(symbol_arity) {
            if let Predicate::Clauses(range) = self.remove(predicate_idx).predicate {
                let step = -((range.1 - range.0) as isize);
                self.update_clause_indexes(step, predicate_idx);
                //Update body list
                let mut body_list_idx = 0;
                while body_list_idx < self.body_list.len() {
                    if self.body_list[body_list_idx] > predicate_idx {
                        self.body_list[body_list_idx] -= 1;
                    } else if self.body_list[body_list_idx] == predicate_idx {
                        self.body_list.remove(body_list_idx);
                    }
                    body_list_idx += 1;
                }

                Some(range)
            } else {
                None
            }
        } else {
            None
        }
    }

    /* Used when clauses are removed or added from the clause table.
     Predicates whose clause index range starts above the affected index
     must have this range shifted either up or down*/
    fn update_clause_indexes(&mut self, step: isize, range_start: usize) {
        for predicate in &mut self[range_start..] {
            predicate.shift_clause_range(step);
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
    pub fn get_body_clauses(&self, arity: usize) -> Vec<(usize, usize)> {
        let mut body_clause_ranges = vec![];

        for &idx in &self.body_list {
            if self[idx].symbol_arity.1 != arity {
                continue;
            }
            if let Predicate::Clauses(range) = self[idx].predicate {
                body_clause_ranges.push(range);
            }
        }

        body_clause_ranges
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
    use crate::program::predicate_table::FindReturn;

    use super::{Predicate, PredicateEntry, PredicateFN, PredicateTable};

    fn setup() -> PredicateTable {
        PredicateTable {
            predicates: vec![
                PredicateEntry {
                    symbol_arity: (1, 2),
                    predicate: Predicate::Clauses((0, 1)),
                },
                PredicateEntry {
                    symbol_arity: (2, 1),
                    predicate: Predicate::Function(PredicateFN),
                },
                PredicateEntry {
                    symbol_arity: (2, 2),
                    predicate: Predicate::Clauses((1, 3)),
                },
                PredicateEntry {
                    symbol_arity: (3, 2),
                    predicate: Predicate::Clauses((3, 5)),
                },
            ],
            body_list: vec![2, 3],
        }
    }

    #[test]
    fn find_predicate() {
        let pred_table = setup();

        assert_eq!(pred_table.find_predicate((2, 1)), FindReturn::Index(1));
        assert_eq!(pred_table.find_predicate((2, 2)), FindReturn::Index(2));
        assert_eq!(pred_table.find_predicate((1, 3)), FindReturn::InsertPos(1));
        assert_eq!(pred_table.find_predicate((1, 1)), FindReturn::InsertPos(0));
        assert_eq!(pred_table.find_predicate((3, 3)), FindReturn::InsertPos(4));
    }

    #[test]
    fn get_predicate() {
        let pred_table = setup();

        assert_eq!(
            pred_table.get_predicate((2, 1)),
            Some(Predicate::Function(PredicateFN)),
        );
        assert_eq!(
            pred_table.get_predicate((2, 2)),
            Some(Predicate::Clauses((1, 3)))
        );
        assert_eq!(pred_table.get_predicate((1, 3)), None);
    }

    #[test]
    fn insert_predicate_function() {
        let mut pred_table = setup();

        pred_table
            .insert_predicate_function((1, 1), PredicateFN)
            .unwrap();
        pred_table
            .insert_predicate_function((2, 1), PredicateFN)
            .unwrap();
        pred_table
            .insert_predicate_function((4, 1), PredicateFN)
            .unwrap();

        assert_eq!(pred_table.find_predicate((1, 1)), FindReturn::Index(0));
        assert_eq!(
            pred_table.get_predicate((1, 1)),
            Some(Predicate::Function(PredicateFN))
        );

        assert_eq!(pred_table.find_predicate((2, 1)), FindReturn::Index(2));
        assert_eq!(
            pred_table.get_predicate((2, 1)),
            Some(Predicate::Function(PredicateFN))
        );

        assert_eq!(pred_table.find_predicate((4, 1)), FindReturn::Index(5));
        assert_eq!(
            pred_table.get_predicate((4, 1)),
            Some(Predicate::Function(PredicateFN))
        );

        assert_eq!(
            pred_table.insert_predicate_function((2, 2), PredicateFN),
            Err("Cannot insert predicate function to clause table predicate")
        );
    }

    #[test]
    fn add_clause_to_predicate() {
        let mut pred_table = setup();

        assert_eq!(
            pred_table.add_clause_to_predicate(2, (1, 2)),
            Err("New clause index was not at end of current range")
        );
        assert_eq!(
            pred_table.add_clause_to_predicate(2, (2, 1)),
            Err("Cannot add clause to function predicate")
        );

        pred_table.add_clause_to_predicate(1, (1, 2)).unwrap();
        pred_table.add_clause_to_predicate(2, (1, 3)).unwrap();
        pred_table.add_clause_to_predicate(3, (1, 3)).unwrap();

        assert_eq!(
            pred_table.predicates,
            [
                PredicateEntry {
                    symbol_arity: (1, 2),
                    predicate: Predicate::Clauses((0, 2)),
                },
                PredicateEntry {
                    symbol_arity: (1, 3),
                    predicate: Predicate::Clauses((2, 4))
                },
                PredicateEntry {
                    symbol_arity: (2, 1),
                    predicate: Predicate::Function(PredicateFN),
                },
                PredicateEntry {
                    symbol_arity: (2, 2),
                    predicate: Predicate::Clauses((4, 6)),
                },
                PredicateEntry {
                    symbol_arity: (3, 2),
                    predicate: Predicate::Clauses((6, 8)),
                },
            ]
        )
    }

    #[test]
    fn delete() {
        let mut pred_table = setup();

        pred_table.remove_predicate((1, 2));
        pred_table.remove_predicate((2, 3));
        pred_table.remove_predicate((3, 2));

        assert_eq!(
            pred_table.predicates,
            [
                PredicateEntry {
                    symbol_arity: (2, 1),
                    predicate: Predicate::Function(PredicateFN),
                },
                PredicateEntry {
                    symbol_arity: (2, 2),
                    predicate: Predicate::Clauses((0, 2)),
                },
            ]
        );

        assert_eq!(pred_table.body_list, [1])
    }

    #[test]
    fn update_body() {
        let mut pred_table = setup();

        assert_eq!(
            pred_table.set_body((2, 1), true),
            Err("Can't set predicate function to body")
        );
        assert_eq!(
            pred_table.set_body((1, 3), true),
            Err("Can't set non existing predicate to body")
        );

        pred_table.set_body((2, 2), false).unwrap();
        pred_table.set_body((1, 2), true).unwrap();

        assert_eq!(pred_table.body_list, [3, 0],);
    }

    #[test]
    fn get_body_clauses() {
        let mut pred_table = setup();
        assert_eq!(pred_table.get_body_clauses(1), []);
        assert_eq!(pred_table.get_body_clauses(2), [(1, 3), (3, 5)]);
    }
}
