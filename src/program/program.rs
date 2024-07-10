use super::{
    clause::{Clause, ClauseType},
    clause_table::ClauseTable,
};
use crate::{
    heap::{heap::Heap, symbol_db::SymbolDB},
    pred_module::{PredModule, PredicateFN},
};
use std::{
    collections::HashMap,
    ops::{Deref, DerefMut, Range},
};

pub enum Predicate {
    Function(PredicateFN),
    Clauses(Range<usize>),
}

pub struct ProgramIterator {
    pub ranges: [Option<Range<usize>>; 4],
}

impl Iterator for ProgramIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        for i in 0..4 {
            if let Some(range) = &mut self.ranges[i] {
                if let Some(i) = range.next() {
                    return Some(i);
                } else {
                    self.ranges[i] = None;
                }
            }
        }
        None
    }
}

pub struct Program {
    pub clauses: ClauseTable,
    pub type_flags: [usize; 4],
    pub predicates: HashMap<(usize, usize), Predicate>, //(id, arity): Predicate
    pub body_preds: Vec<(usize, usize)>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            clauses: ClauseTable::new(),
            type_flags: [0; 4],
            predicates: HashMap::new(),
            body_preds: Vec::new(),
        }
    }

    /**Make a symbol and arity be allowed to match with variable predicate symbol goals */
    pub fn add_body_pred(&mut self, symbol: usize, arity: usize, store: &impl Heap) {
        self.organise_clause_table(store);
        self.body_preds.push((symbol, arity));
        if let Some(Predicate::Clauses(clauses)) = self.predicates.get(&(symbol, arity)) {
            for clause in clauses.clone() {
                self.clauses.set_body(clause)
            }
        }

        self.organise_clause_table(store);
    }

    pub fn add_clause(&mut self, mut clause: Clause, store: &impl Heap) {
        let sym_arr = store.str_symbol_arity(clause[0]);
        if self.body_preds.contains(&sym_arr) {
            clause.clause_type = ClauseType::BODY;
        }
        self.clauses.add_clause(clause);
    }

    /** Load a module with predicate functions */
    pub fn add_pred_module(&mut self, pred_module: PredModule) {
        for (symbol, arity, predfn) in pred_module {
            let symbol = SymbolDB::set_const(symbol);
            self.predicates
                .insert((symbol, *arity + 1), Predicate::Function(*predfn));
        }
    }

    /** Build a map from (symbol, arity) -> Range of indicies for clauses
     * This works as long as we sort the clause table
     */
    pub fn predicate_map(&self, store: &impl Heap) -> HashMap<(usize, usize), Range<usize>> {
        let mut predicate_map = HashMap::<(usize, usize), (usize, usize)>::new();

        for (i, clause) in self.clauses.iter().enumerate() {
            let (symbol, arity) = store.str_symbol_arity(clause[0]);
            match predicate_map.get_mut(&(symbol, arity)) {
                Some((_, len)) => *len += 1,
                None => {
                    predicate_map.insert((symbol, arity), (i, 1));
                }
            }
        }

        predicate_map
            .into_iter()
            .map(|(k, v)| (k, v.0..v.0 + v.1))
            .collect()
    }

    //**Sort the clause table, find type flags, and build predicate map*/
    pub fn organise_clause_table(&mut self, store: &impl Heap) {
        self.clauses.sort_clauses(store);
        self.type_flags = self.clauses.find_flags();
        self.predicates.extend(
            self.predicate_map(store)
                .into_iter()
                .map(|(k, v)| (k, Predicate::Clauses(v))),
        )
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn get(&self, index: usize) -> Clause {
        self.clauses.get(index)
    }
    pub fn print_predicates(&self){
        for (symbol, arity) in self.predicates.keys(){
            println!("{}/{arity}",SymbolDB::get_symbol(*symbol));
        }
    }
}

impl Deref for Program {
    type Target = ClauseTable;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for Program {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}

unsafe impl Send for Program {}
unsafe impl Sync for Program {}
