use std::{
    cmp::{self, PartialOrd},
    ops::{Deref, DerefMut, Range},
};

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
    predicate: PredClFn,
}

pub struct PredicateTable(Vec<Predicate>);

impl PredicateTable {
    pub fn find_predicate(&self, symbol_arity: &SymbolArity) -> Result<usize, usize> {
        let mut lb: usize = 0;
        let mut ub: usize = self.len() - 1;
        let mut mid: usize;
        while ub > lb {
            mid = (lb + ub) / 2;
            match symbol_arity.cmp(&self[mid].symbol_arity) {
                std::cmp::Ordering::Less => ub = mid - 1,
                std::cmp::Ordering::Equal => return Ok(mid),
                std::cmp::Ordering::Greater => lb = mid + 1,
            }
        }
        match symbol_arity.cmp(&self[lb].symbol_arity) {
            cmp::Ordering::Less => Err(lb),
            cmp::Ordering::Equal => Ok(lb),
            cmp::Ordering::Greater => Err(lb + 1),
        }
    }

    pub fn update_insert_predicate(
        &mut self,
        symbol: usize,
        arity: usize,
        body: bool,
        predicate: PredClFn,
    ) {
        let symbol_arity = (symbol, arity);
        match self.find_predicate(&symbol_arity) {
            Ok(i) => {
                self[i] = Predicate {
                    symbol_arity,
                    body,
                    predicate,
                }
            }
            Err(new_i) => self.insert(
                new_i,
                Predicate {
                    symbol_arity,
                    body,
                    predicate,
                },
            ),
        }
    }

    pub fn get_predicate(&self, symbol: usize, arity: usize) -> Option<&Predicate> {
        match self.find_predicate(&(symbol, arity)) {
            Ok(i) => Some(&self[i]),
            Err(_) => None,
        }
    }

    pub fn delete(&mut self, symbol: usize, arity: usize) {
        if let Ok(index) = self.find_predicate(&(symbol, arity)) {
            self.0.remove(index);
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
    use super::{PredClFn, Predicate, PredicateTable};

    #[test]
    fn find_predicate() {
        let body = true;
        let pred_table = PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (3, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
        ]);

        assert_eq!(pred_table.find_predicate(&(2, 1)), Ok(1));
        assert_eq!(pred_table.find_predicate(&(2, 2)), Ok(2));
        assert_eq!(pred_table.find_predicate(&(1, 3)), Err(1));
        assert_eq!(pred_table.find_predicate(&(1, 1)), Err(0));
        assert_eq!(pred_table.find_predicate(&(3, 3)), Err(4));
    }

    #[test]
    fn get_predicate() {
        let body = true;
        let pred_table = PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (3, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
        ]);

        assert_eq!(
            pred_table.get_predicate(2, 1),
            Some(&Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            })
        );
        assert_eq!(pred_table.get_predicate(1, 3), None);
    }

    #[test]
    fn insert() {
        let body = true;
        let mut pred_table = PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (3, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
        ]);

        pred_table.update_insert_predicate(1, 1, true, PredClFn::Clauses(0..1));
        pred_table.update_insert_predicate(2, 3, true, PredClFn::Clauses(0..1));
        pred_table.update_insert_predicate(4, 1, true, PredClFn::Clauses(0..1));

        assert_eq!(pred_table.find_predicate(&(1, 1)), Ok(0));
        assert_eq!(pred_table.find_predicate(&(2, 3)), Ok(4));
        assert_eq!(pred_table.find_predicate(&(4, 1)), Ok(6));

        assert_eq!(
            pred_table.0,
            [
                Predicate {
                    symbol_arity: (1, 1),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (1, 2),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (2, 1),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (2, 2),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (2, 3),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (3, 2),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
                Predicate {
                    symbol_arity: (4, 1),
                    body,
                    predicate: PredClFn::Clauses(0..1)
                },
            ]
        );
    }

    #[test]
    fn update() {
        let body = true;
        let mut pred_table = PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (3, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
        ]);

        pred_table.update_insert_predicate(1, 2, false, PredClFn::Clauses(5..7));

        assert_eq!(
            pred_table.get_predicate(1, 2),
            Some(&Predicate {
                symbol_arity: (1, 2),
                body: false,
                predicate: PredClFn::Clauses(5..7),
            })
        );
    }

    #[test]
    fn delete() {
        let body = true;
        let mut pred_table = PredicateTable(vec![
            Predicate {
                symbol_arity: (1, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 1),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (2, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
            Predicate {
                symbol_arity: (3, 2),
                body,
                predicate: PredClFn::Clauses(0..1),
            },
        ]);

        pred_table.delete(1, 2);
        pred_table.delete(2, 3);
        pred_table.delete(3, 2);

        assert_eq!(
            pred_table.0,
            [
                Predicate {
                    symbol_arity: (2, 1),
                    body,
                    predicate: PredClFn::Clauses(0..1),
                },
                Predicate {
                    symbol_arity: (2, 2),
                    body,
                    predicate: PredClFn::Clauses(0..1),
                },
            ]
        );
    }
}
