use super::{
    clause::{Clause, ClauseType},
    clause_table::ClauseTable,
    hypothesis::Hypothesis,
};
use crate::{
    heap::{
        heap::Heap,
        store::{Store, Tag},
        symbol_db::SymbolDB,
    },
    interface::config::Config,
    pred_module::{config_mod, PredModule, PredicateFN},
};
use manual_rwlock::ReadGaurd;
use std::{
    collections::HashMap,
    ops::{Deref, DerefMut, Range},
};

enum Predicate {
    Function(PredicateFN),
    Clauses(Range<usize>),
}
pub enum CallRes {
    Function(PredicateFN),
    Clauses(ProgramIterator),
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
    clauses: ClauseTable,
    type_flags: [usize; 4],
    predicates: HashMap<(usize, usize), Predicate>, //(id, arity): Predicate
    body_preds: Vec<(usize, usize)>,
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

pub enum ProgH<'a> {
    Dynamic(Hypothesis),
    Static(&'a Hypothesis),
    None,
}

impl<'a> ProgH<'a> {
    pub fn len(&self) -> usize {
        match self {
            ProgH::Dynamic(h) => h.len(),
            ProgH::Static(h) => h.len(),
            ProgH::None => 0,
        }
    }
}

impl<'a> Deref for ProgH<'a>{
    type Target = Hypothesis;
    fn deref(&self) -> &Self::Target {
        match self {
            ProgH::Dynamic(h) => h,
            ProgH::Static(h) => h,
            ProgH::None => panic!(),
        }
    }
}

impl <'a> DerefMut for ProgH<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        if let ProgH::Dynamic(h) = self{
            h
        }else{
            panic!("can mutably access this hypothesis")
        }
    }
}
pub struct DynamicProgram<'a> {
    pub hypothesis: ProgH<'a>,
    pub prog: ReadGaurd<'a, Program>,
}

impl<'a> DynamicProgram<'a> {
    pub fn new(hypothesis: ProgH<'a>, prog: ReadGaurd<'a, Program>) -> DynamicProgram<'a> {
        match hypothesis {
            ProgH::Static(_) => DynamicProgram { hypothesis, prog },
            ProgH::Dynamic(_) => DynamicProgram { hypothesis, prog },
            ProgH::None => DynamicProgram {
                hypothesis: ProgH::Dynamic(Hypothesis::new()),
                prog,
            },
        }
    }

    /** Takes goals and returns either a predicate function of an interator over clause indices */
    pub fn call(&self, goal_addr: usize, store: &impl Heap, config: Config) -> CallRes {
        if store[goal_addr].0 == Tag::Lis {
            return CallRes::Function(config_mod::load_file);
        }
        let (mut symbol, arity) = store.str_symbol_arity(goal_addr);
        if symbol < Store::CON_PTR {
            symbol = store[store.deref_addr(symbol)].1;
        }
        match self.prog.predicates.get(&(symbol, arity)) {
            Some(Predicate::Function(function)) => CallRes::Function(*function),
            Some(Predicate::Clauses(range)) => CallRes::Clauses(ProgramIterator {
                ranges: [Some(range.clone()), None, None, None].into(),
            }), //TO DO sort clause table so that this can be range
            None => {
                let mut c_types = if symbol < Store::CON_PTR {
                    if self.hypothesis.len() == config.max_h_clause
                        || self.hypothesis.invented_preds == config.max_h_pred
                    {
                        [false, true, false, true]
                    } else {
                        [false, true, true, true]
                    }
                } else {
                    if self.hypothesis.len() == config.max_h_clause {
                        [false, false, false, true]
                    } else {
                        [false, false, true, true]
                    }
                };
                if !config.learn {
                    c_types[2] = false;
                }
                CallRes::Clauses(self.iter(c_types))
            }
        }
    }

    /**Creates an iterator over the clause indices that have a type within c_types
     * @c_types: array of the bool enum determining which clause types to iterate over
     *  [Clause, Body, Meta, Hypothesis]
     */
    pub fn iter(&self, c_types: [bool; 4]) -> ProgramIterator {
        const ARRAY_REPEAT_VALUE: Option<Range<usize>> = None;
        let mut ranges = [ARRAY_REPEAT_VALUE; 4];
        if c_types[0] {
            ranges[0] = Some(0..self.prog.type_flags[1]);
        }
        if c_types[1] {
            ranges[1] = Some(self.prog.type_flags[1]..self.prog.type_flags[2]);
        }
        if c_types[2] {
            ranges[2] = Some(self.prog.type_flags[2]..self.prog.type_flags[3]);
        }
        if c_types[3] {
            ranges[3] = Some(self.prog.type_flags[3]..self.len());
        }
        ProgramIterator { ranges }
    }

    pub fn len(&self) -> usize {
        self.prog.len() + self.hypothesis.len()
    }

    pub fn get(&self, index: usize) -> Clause {
        if index < self.prog.len() {
            self.prog.get(index)
        } else {
            self.hypothesis.get(index - self.prog.len())
        }
    }
}
