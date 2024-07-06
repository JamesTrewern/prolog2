use std::ops::{Deref, DerefMut, Range};

use manual_rwlock::ReadGaurd;

use crate::{
    heap::{
        heap::Heap,
        store::{Store, Tag},
        symbol_db::SymbolDB,
    },
    interface::config::Config,
    pred_module::{config_mod, PredicateFN},
    resolution::unification::Binding,
};

use super::{
    clause::Clause,
    clause_table::ClauseTable,
    program::{Predicate, Program, ProgramIterator},
};

const PRED_NAME: &'static str = "pred";

pub enum CallRes {
    Function(PredicateFN),
    Clauses(ProgramIterator),
}

pub enum Hypothesis<'a> {
    Dynamic(ClauseTable),
    Static(&'a ClauseTable),
    None,
}

impl<'a> Hypothesis<'a> {
    pub fn len(&self) -> usize {
        match self {
            Hypothesis::Dynamic(h) => h.len(),
            Hypothesis::Static(h) => h.len(),
            Hypothesis::None => 0,
        }
    }
}

impl<'a> Deref for Hypothesis<'a> {
    type Target = ClauseTable;
    fn deref(&self) -> &Self::Target {
        match self {
            Hypothesis::Dynamic(h) => h,
            Hypothesis::Static(h) => h,
            Hypothesis::None => panic!(),
        }
    }
}

impl<'a> DerefMut for Hypothesis<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        if let Hypothesis::Dynamic(h) = self {
            h
        } else {
            panic!("can mutably access this hypothesis")
        }
    }
}
pub struct DynamicProgram<'a> {
    pub hypothesis: Hypothesis<'a>,
    pub prog: ReadGaurd<'a, Program>,
    constraints: Vec<Box<[(usize, usize)]>>,
    pub invented_preds: usize,
}

impl<'a> DynamicProgram<'a> {
    pub fn new(hypothesis: Hypothesis<'a>, prog: ReadGaurd<'a, Program>) -> DynamicProgram<'a> {
        match hypothesis {
            Hypothesis::None => DynamicProgram {
                hypothesis: Hypothesis::Dynamic(ClauseTable::new()),
                prog,
                constraints: Vec::new(),
                invented_preds: 0,
            },
            _ => DynamicProgram {
                hypothesis,
                prog,
                constraints: Vec::new(),
                invented_preds: 0,
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
                        || self.invented_preds == config.max_h_pred
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
        self.hypothesis.add_clause(clause);

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
        let i = self.hypothesis.len() - 1;
        self.hypothesis.remove_clause(i);

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
        for i in 0..self.hypothesis.len() {
            self.hypothesis.get(i).normalise(heap);
        }
    }
}
