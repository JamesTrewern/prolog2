use std::{cmp::Ordering, ops::{Deref, DerefMut, Range}};

pub(crate) type SymbolArity = (usize, usize);

//TODO create predicate function type
#[derive(PartialEq, Eq, Debug)]
pub struct PredicateFN;
#[derive(PartialEq, Eq, Debug)]
pub enum PredClFn {
    Function(PredicateFN),
    Clauses(Range<usize>),
}

#[derive(PartialEq, Eq, Debug)]
pub struct Predicate {
    symbol_arity: SymbolArity,
    body: bool,
    pub predicate: PredClFn,
}

impl Predicate {
    pub fn shift_clause_range(&mut self, step: isize) {
        if let PredClFn::Clauses(range) = &mut self.predicate {
            range.start = (range.start as isize + step) as usize;
            range.end = (range.end as isize + step) as usize;
        }
    }
}

pub struct PredicateTable(Vec<Predicate>);

#[derive(Debug, PartialEq, Eq)]
enum FindReturn {
    Index(usize),
    InsertPos(usize),
}

impl PredicateTable {
    pub fn new() -> Self {
        PredicateTable(vec![])
    }

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

    pub fn insert_predicate_function(
        &mut self,
        symbol_arity: SymbolArity,
        predicate_fn: PredicateFN,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self[idx].predicate {
                PredClFn::Function(old_predicate_fn) => {
                    *old_predicate_fn = predicate_fn;
                    Ok(())
                }
                _ => Err("Cannot insert predicate function to clause table predicate"),
            },
            FindReturn::InsertPos(insert_idx) => {
                self.insert(
                    insert_idx,
                    Predicate {
                        symbol_arity,
                        body: false,
                        predicate: PredClFn::Function(predicate_fn),
                    },
                );
                Ok(())
            }
        }
    }

    pub fn add_clause_to_predicate(
        &mut self,
        clause_idx: usize,
        symbol_arity: SymbolArity,
    ) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => match &mut self.get_mut(idx).unwrap().predicate {
                PredClFn::Function(_) => return Err("Cannot add clause to function predicate"),
                PredClFn::Clauses(range) => {
                    if range.end == clause_idx {
                        range.end += 1;
                        for predicate in &mut self.0[idx + 1..] {
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
                    Predicate {
                        symbol_arity,
                        body: false,
                        predicate: PredClFn::Clauses(clause_idx..clause_idx + 1),
                    },
                );
                for predicate in &mut self.0[insert_idx + 1..] {
                    predicate.shift_clause_range(1);
                }
            }
        };
        Ok(())
    }

    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<&Predicate> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(i) => Some(&self[i]),
            FindReturn::InsertPos(_) => None,
        }
    }

    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) -> Option<Range<usize>> {
        if let FindReturn::Index(index) = self.find_predicate(symbol_arity) {
            if let PredClFn::Clauses(range) = self.0.remove(index).predicate {
                let step = -((range.end - range.start) as isize);
                self.update_clause_indexes(step, index);
                Some(range)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn update_clause_indexes(&mut self, step: isize, range_start: usize) {
        for predicate in &mut self.0[range_start..] {
            predicate.shift_clause_range(step);
        }
    }

    pub fn set_body(&mut self, symbol_arity: SymbolArity, value: bool) -> Result<(), &str> {
        match self.find_predicate(symbol_arity) {
            FindReturn::Index(idx) => {
                let predicate = &mut self.0[idx];
                if matches!(predicate.predicate, PredClFn::Function(_)) {
                    Err("Can't set predicate function to body")
                } else {
                    predicate.body = value;
                    Ok(())
                }
            }
            _ => Err("Can't set non existing predicate to body"),
        }
    }
}

impl Deref for PredicateTable {
    type Target = Vec<Predicate>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for PredicateTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::program::predicate_table::FindReturn;

    use super::{PredClFn, Predicate, PredicateFN, PredicateTable};

    fn setup() -> PredicateTable {
        PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body: false,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body: false,
                predicate: PredClFn::Function(PredicateFN),
            },
            Predicate {
                symbol_arity: (2, 2),
                body: false,
                predicate: PredClFn::Clauses(1..3),
            },
            Predicate {
                symbol_arity: (3, 2),
                body: false,
                predicate: PredClFn::Clauses(3..5),
            },
        ])
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
            Some(&Predicate {
                symbol_arity: (2, 1),
                body: false,
                predicate: PredClFn::Function(PredicateFN),
            })
        );
        assert_eq!(
            pred_table.get_predicate((2, 2)),
            Some(&Predicate {
                symbol_arity: (2, 2),
                body: false,
                predicate: PredClFn::Clauses(1..3),
            })
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
            Some(&Predicate {
                symbol_arity: (1, 1),
                body: false,
                predicate: PredClFn::Function(PredicateFN)
            })
        );

        assert_eq!(pred_table.find_predicate((2, 1)), FindReturn::Index(2));
        assert_eq!(
            pred_table.get_predicate((2, 1)),
            Some(&Predicate {
                symbol_arity: (2, 1),
                body: false,
                predicate: PredClFn::Function(PredicateFN)
            })
        );

        assert_eq!(pred_table.find_predicate((4, 1)), FindReturn::Index(5));
        assert_eq!(
            pred_table.get_predicate((4, 1)),
            Some(&Predicate {
                symbol_arity: (4, 1),
                body: false,
                predicate: PredClFn::Function(PredicateFN)
            })
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
            pred_table.0,
            [
                Predicate {
                    symbol_arity: (1, 2),
                    body: false,
                    predicate: PredClFn::Clauses(0..2),
                },
                Predicate {
                    symbol_arity: (1, 3),
                    body: false,
                    predicate: PredClFn::Clauses(2..4)
                },
                Predicate {
                    symbol_arity: (2, 1),
                    body: false,
                    predicate: PredClFn::Function(PredicateFN),
                },
                Predicate {
                    symbol_arity: (2, 2),
                    body: false,
                    predicate: PredClFn::Clauses(4..6),
                },
                Predicate {
                    symbol_arity: (3, 2),
                    body: false,
                    predicate: PredClFn::Clauses(6..8),
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
            pred_table.0,
            [
                Predicate {
                    symbol_arity: (2, 1),
                    body: false,
                    predicate: PredClFn::Function(PredicateFN),
                },
                Predicate {
                    symbol_arity: (2, 2),
                    body: false,
                    predicate: PredClFn::Clauses(0..2),
                },
            ]
        );
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

        pred_table.set_body((2, 2), true).unwrap();

        assert_eq!(
            pred_table.get_predicate((2, 2)),
            Some(&Predicate {
                symbol_arity: (2, 2),
                body: true,
                predicate: PredClFn::Clauses(1..3),
            })
        );
    }
}
