use super::{clause::{Clause, ClauseType}, clause_table::{ClauseIterator, ClauseTable}};
use crate::{heap::heap::{Heap, Tag}, interface::config::Config, pred_module::{config, PredModule, PredicateFN}, resolution::unification::Binding};
use std::{collections::HashMap, ops::Range};

const PRED_NAME: &'static str = "James";

enum Predicate {
    Function(PredicateFN),
    Clauses(Range<usize>),
}

pub enum CallRes {
    Function(PredicateFN),
    Clauses(ClauseIterator),
}
pub struct Program {
    pub clauses: ClauseTable,
    predicates: HashMap<(usize, usize), Predicate>, //(id, arity): Predicate
    constraints: Vec<Box<[(usize, usize)]>>,
    invented_preds: usize,
    pub h_size: usize,
    body_preds: Vec<(usize, usize)>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            predicates: HashMap::new(),
            // predicate_functions: HashMap::new(),
            clauses: ClauseTable::new(),
            invented_preds: 0,
            h_size: 0,
            constraints: vec![],
            body_preds: vec![],
        }
    }

    /** Takes goals and returns either a predicate function of an interator over clause indices */
    pub fn call(&mut self, goal_addr: usize, heap: &mut Heap, config: &mut Config) -> CallRes {

        if heap[goal_addr].0 == Tag::LIS{
            return CallRes::Function(config::load_file);
        }
        let (mut symbol, arity) = heap.str_symbol_arity(goal_addr);
        if symbol < Heap::CON_PTR {
            symbol = heap[heap.deref_addr(symbol)].1;
        }

        match self.predicates.get(&(symbol, arity)) {
            Some(Predicate::Function(function)) => CallRes::Function(*function),
            Some(Predicate::Clauses(range)) => CallRes::Clauses(ClauseIterator { ranges: [range.clone()].into()}), //TO DO sort clause table so that this can be range
            None => {
                let mut c_types = if symbol < Heap::CON_PTR {
                    if self.h_size == config.max_h_clause
                        || self.invented_preds == config.max_h_pred
                    {
                        [false, true, false, true]
                    } else {
                        [false, true, true, true]
                    }
                } else {
                    if self.h_size == config.max_h_clause {
                        [false,false,false,true]
                    } else {
                        [false,false,true,true]
                    }
                };
                if !config.learn{
                    c_types[2] = false;
                }
                CallRes::Clauses(self.clauses.iter(c_types))
            }
        }
    }

    /**Make a symbol and arity be allowed to match with variable predicate symbol goals */
    pub fn add_body_pred(&mut self, symbol: usize, arity: usize, heap: &Heap) {
        self.organise_clause_table(heap);
        self.body_preds.push((symbol, arity));
        if let Some(Predicate::Clauses(clauses)) = self.predicates.get(&(symbol, arity)) {
            for clause in clauses.clone() {
                self.clauses.set_body(clause)
            }
        }
        self.organise_clause_table(heap);
    }

    pub fn add_clause(&mut self, mut clause: Clause, heap: &Heap) {
        let sym_arr = heap.str_symbol_arity(clause[0]);
        if self.body_preds.contains(&sym_arr) {
            clause.clause_type = ClauseType::BODY;
        }
        self.clauses.add_clause(clause);
    }

    /**Add clause to hypothesis, If invented predicate symbol return true*/
    pub fn add_h_clause(&mut self, clause: Clause, heap: &mut Heap) -> Option<usize> {
        //Build contraints for new clause. This assumes that no unifcation should happen between variable predicate symbols
        let mut constraints = Vec::<(usize, usize)>::new();
        for i in 0..clause.len() {
            for j in i..clause.len() {
                match (heap[clause[i] + 1], heap[clause[j] + 1]) {
                    ((Tag::REF, addr1), (Tag::REF, addr2)) if addr1 != addr2 => {
                        constraints.push((clause[i] + 1, clause[j] + 1));
                        constraints.push((clause[j] + 1, clause[i] + 1));
                    }
                    ((Tag::REF, addr1), (Tag::CON, addr2)) if addr1 != addr2 => {
                        constraints.push((clause[i] + 1, clause[j] + 1))
                    }
                    ((Tag::CON, addr1), (Tag::REF, addr2)) if addr1 != addr2 => {
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
        self.h_size += 1;

        //If head predicate is variable invent new symbol
        if symbol < Heap::CON_PTR {
            self.invented_preds += 1;
            symbol = heap.add_const_symbol(&format!("{PRED_NAME}_{}", self.invented_preds));
            Some(heap.set_const(symbol))
        } else {
            None
        }
    }

    /**Remove clause from hypothesis */
    pub fn remove_h_clause(&mut self, invented: bool) {
        self.h_size -= 1;
        if invented {
            self.invented_preds -= 1;
        }
        self.clauses.remove_clause(self.clauses.clauses.len() - 1);
        self.constraints.pop();
    }

    /**Check if binding will unify variable predicate symbols inside a H clause */
    pub fn check_constraints(&self, binding: &Binding, heap: &Heap) -> bool {
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
    pub fn symbolise_hypothesis(&self, heap: &mut Heap) {
        //TO DO could turn unbound refs in H into constants
        for i in self.clauses.iter([false,false,false,true]) {
            self.clauses.get(i).symbolise_vars(heap);
        }
    }

    /** Load a module with predicate functions */
    pub fn add_pred_module(&mut self, pred_module: PredModule, heap: &mut Heap) {
        for (symbol, arity, predfn) in pred_module {
            let symbol = heap.add_const_symbol(symbol);
            self.predicates
                .insert((symbol, *arity), Predicate::Function(*predfn));
        }
    }

    //**Sort the clause table, find type flags, and build predicate map*/
    pub fn organise_clause_table(&mut self, heap: &Heap) {
        self.clauses.sort_clauses(heap);
        self.clauses.find_flags();
        self.predicates.extend(
            self.clauses
                .predicate_map(heap)
                .into_iter()
                .map(|(k, v)| (k, Predicate::Clauses(v))),
        )
    }
}

