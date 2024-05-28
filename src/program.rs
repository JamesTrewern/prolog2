use std::collections::HashMap;

use crate::{
    choice::Choice,
    clause::*,
    clause_table::ClauseTable,
    heap::Tag,
    pred_module::{PredModule, PredicateFN},
    state::Config,
    unification::*,
    Heap,
};

const PRED_NAME: &'static str = "James";

pub struct Program {
    pub predicate_functions: HashMap<(usize, usize), PredicateFN>,
    pub predicates: HashMap<(usize, usize), Box<[usize]>>, //(id, arity): Predicate
    pub clauses: ClauseTable,
    pub constraints: Vec<Box<[(usize, usize)]>>,
    pub invented_preds: usize,
    pub h_size: usize,
    pub body_preds: Vec<(usize, usize)>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            predicates: HashMap::new(),
            predicate_functions: HashMap::new(),
            clauses: ClauseTable::new(),
            invented_preds: 0,
            h_size: 0,
            constraints: vec![],
            body_preds: vec![],
        }
    }

    fn match_clause(
        &self,
        clause_i: usize,
        clause_type: ClauseType,
        clause: &Clause,
        goal_addr: usize,
        heap: &Heap,
    ) -> Option<Choice> {
        if let Some(binding) = unify(clause[0], goal_addr, heap) {
            if clause_type != ClauseType::CLAUSE {
                if self.check_constraints(&binding, heap) {
                    return None;
                }
            }
            Some(Choice {
                clause: clause_i,
                binding,
                new_clause: clause_type == ClauseType::META,
            })
        } else {
            None
        }
    }

    pub fn call_predfn(
        &mut self,
        goal_addr: usize,
        heap: &mut Heap,
        config: &mut Config,
    ) -> Option<bool> {
        let (symbol, arity) = heap.str_symbol_arity(goal_addr);
        if let Some(predfn) = self.predicate_functions.get(&(symbol, arity)) {
            Some(predfn(goal_addr, heap, config, self))
        } else {
            None
        }
    }

    pub fn call(&mut self, goal_addr: usize, heap: &mut Heap, config: &mut Config) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];

        if let Some(res) = self.call_predfn(goal_addr, heap, config) {
            if res {
                return vec![Choice {
                    clause: Heap::CON_PTR,
                    binding: vec![],
                    new_clause: false,
                }];
            } else {
                return vec![];
            }
        }

        let (mut symbol, arity) = heap.str_symbol_arity(goal_addr);
        if symbol < Heap::CON_PTR {
            symbol = heap[heap.deref_addr(symbol)].1;
        }

        if let Some(clauses) = self.predicates.get(&(symbol, arity)) {
            for i in clauses.iter() {
                let (clause_type, clause) = self.clauses.get(*i);
                if let Some(choice) = self.match_clause(*i, clause_type, clause, goal_addr, heap) {
                    choices.push(choice)
                }
            }
        } else {
            let iterator = if symbol < Heap::CON_PTR {
                if self.h_size == config.max_h_clause || self.invented_preds == config.max_h_pred {
                    self.clauses
                        .iter(&[ClauseType::BODY, ClauseType::HYPOTHESIS])
                } else {
                    self.clauses
                        .iter(&[ClauseType::BODY, ClauseType::META, ClauseType::HYPOTHESIS])
                }
            } else {
                if self.h_size == config.max_h_clause {
                    self.clauses.iter(&[ClauseType::HYPOTHESIS])
                } else {
                    self.clauses
                        .iter(&[ClauseType::META, ClauseType::HYPOTHESIS])
                }
            };
            //TO DO use clause returned by iterator
            for i in iterator {
                let (clause_type, clause) = self.clauses.get(i);
                if let Some(choice) = self.match_clause(i, clause_type, clause, goal_addr, heap) {
                    choices.push(choice);
                }
            }
        }
        choices
    }

    pub fn add_body_pred(&mut self, symbol: usize, arity: usize, heap: &Heap) {
        self.organise_clause_table(heap);
        self.body_preds.push((symbol, arity));
        if let Some(clauses) = self.predicates.get(&(symbol, arity)) {
            for clause in clauses.iter() {
                self.clauses.set_body(*clause)
            }
        }
        self.organise_clause_table(heap);
    }

    pub fn add_clause(&mut self, clause_type: ClauseType, clause: Box<Clause>) {
        self.clauses.add_clause(clause, clause_type);
    }

    //Add clause, If invented predicate symbol return true
    pub fn add_h_clause(
        &mut self,
        clause: Box<Clause>,
        heap: &mut Heap,
    ) -> Option<usize> {
        //Build contraints for new clause. This assumes that no unifcation should happen between variable predicate symbols 
        let mut constraints = Vec::<(usize,usize)>::new();
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
        self.clauses.add_clause(clause, ClauseType::HYPOTHESIS);
        self.h_size += 1;

        //If head predicate is variable invent new symbol
        if symbol < Heap::CON_PTR {
            self.invented_preds += 1;
            symbol = heap.add_const_symbol(&format!("{PRED_NAME}_{}", self.invented_preds));
            Some(heap.set_const(symbol))
        }else{
            None
        }
    }

    pub fn remove_h_clause(&mut self, invented: bool) {
        self.h_size -= 1;
        if invented {
            self.invented_preds -= 1;
        }
        self.clauses.remove_clause(self.clauses.clauses.len() - 1);
        self.constraints.pop();
    }

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

    pub fn symbolise_hypothesis(&self, heap: &mut Heap) {
        //TO DO could turn unbound refs in H into constants
        for i in self.clauses.iter(&[ClauseType::HYPOTHESIS]) {
            self.clauses.get(i).1.symbolise_vars(heap);
        }
    }

    pub fn add_pred_module(&mut self, pred_module: PredModule, heap: &mut Heap) {
        for (symbol, arity, predfn) in pred_module {
            let symbol = heap.add_const_symbol(symbol);
            self.predicate_functions.insert((symbol, *arity), *predfn);
        }
    }

    pub fn organise_clause_table(&mut self, heap: &Heap) {
        self.clauses.sort_clauses();
        self.clauses.find_flags();
        self.predicates = self.clauses.predicate_map(heap)
    }
}

