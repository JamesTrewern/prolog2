use crate::{
    binding::{Binding, BindingTraits},
    heap::Heap,
    state::{Config, State},
    unification::unify,
};
use std::{collections::HashMap, ops::Index, usize, vec};

const PRED_NAME: &'static str = "James";

use super::{
    choice::Choice,
    clause::{self, Clause, ClauseOwned, ClauseTable, ClauseTraits, ClauseType},
};
pub type PredicateFN = fn(Box<[usize]>, &mut Heap) -> bool;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];

pub struct Program {
    predicate_functions: HashMap<(usize,usize), PredicateFN>,
    pub predicates: HashMap<(usize, usize), Vec<usize>>, //(id, arity): Predicate
    pub clauses: ClauseTable,
    invented_preds: usize,
    pub h_clauses: usize,
}

impl Program {
    pub fn new() -> Program {
        Program {
            predicates: HashMap::new(),
            predicate_functions: HashMap::new(),
            clauses: ClauseTable::new(),
            invented_preds: 0,
            h_clauses: 0,
        }
    }
    // pub fn add_module(&mut self, pred_module: PredModule, heap: &mut Heap) {
    //     for (symbol, arity, f) in pred_module {
    //         let id = heap.add_const_symbol(symbol);
    //         self.predicates
    //             .insert((id, *arity), Predicate::FUNCTION(*f));
    //     }
    // }

    pub fn handle_directive(&mut self, directive: &str) {}

    fn match_clause(&self, clause_i: usize, goal_addr: usize, heap: &Heap) -> Option<Choice> {
        let (clause_type, clause) = self.clauses.get(clause_i);
        if let Some(binding) = unify(clause[0], goal_addr, heap) {
            Some(Choice {
                clause: clause_i,
                binding,
                new_clause: clause_type == ClauseType::META,
                check_contraint: clause_type == ClauseType::HYPOTHESIS,
            })
        } else {
            println!("Failed to match {}", clause.to_string(heap));
            None
        }
    }

    pub fn call(&mut self, goal_addr: usize, heap: &mut Heap) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];

        let (mut symbol, arity) = heap[goal_addr];
        if symbol < Heap::CON_PTR {
            symbol = heap[heap.deref(symbol)].1;
        }

        if let Some(clauses) = self.predicates.get(&(symbol, arity)) {
            for i in clauses.iter() {
                if let Some(choice) = self.match_clause(*i, goal_addr, heap) {
                    choices.push(choice)
                }
            }
        } else {
            let iterator = if symbol < Heap::CON_PTR {
                self.clauses.iter([false,false,true,true,true])
            } else {
                self.clauses.iter([false,false,false,true,true])
            };
            //TO DO use clause returned by iterator
            for (i,_) in iterator {
                if let Some(choice) = self.match_clause(i, goal_addr, heap) {
                    choices.push(choice);
                }
            }
        }
        choices
    }

    pub fn add_clause(&mut self, clause: ClauseOwned, heap: &Heap) {
        let clause_type = if clause.higher_order(heap) {
            ClauseType::META
        } else {
            ClauseType::BODY
        };
        self.clauses.add_clause(clause, clause_type);
    }

    //Add clause, If invented predicate symbol return true
    pub fn add_h_clause(
        &mut self,
        clause: ClauseOwned,
        heap: &mut Heap,
        config: &Config,
    ) -> Option<Option<usize>> {
        if self.h_clauses == config.max_clause {
            println!("Max H size can't add clause");
            return None;
        }
        let symbol = clause.pred_symbol(heap);

        let id = if symbol < Heap::CON_PTR {
            if self.invented_preds == config.max_invented {
                println!("Max invented predicates can't add clause");
                return None;
            }
            self.invented_preds += 1;
            let symbol_id = heap.add_const_symbol(&format!("{PRED_NAME}_{}", self.invented_preds));
            Some(symbol_id)
            // Some(heap.set_const(symbol_id))
        } else {
            //New Clause, No invented predicate symbol
            None
        };

        self.clauses.add_clause(clause, ClauseType::HYPOTHESIS);
        self.h_clauses += 1;

        Some(id)
    }

    pub fn remove_h_clause(&mut self, invented: bool) {
        if invented {
            self.invented_preds -= 1;
        }
        self.clauses.remove_clause(self.clauses.clauses.len() - 1)
    }

    pub fn add_constraint(&mut self, clause: ClauseOwned) {
        self.clauses.add_clause(clause, ClauseType::CONSTRAINT);
    }

    pub fn check_constraints(&self, clause: usize, heap: &Heap) -> bool {
        !self
            .clauses
            .iter([true,false,false,false,false])
            .any(|(i,(_, constraint))| {println!("constraint: {}",constraint.to_string(heap)); constraint.subsumes(&self.clauses.get(clause).1, heap)})
    }

    pub fn write_prog(&self, heap: &Heap) {
        for (i,(c_type, clause)) in self.clauses.iter([true,true,true,true,false]){
            println!("{c_type:?}, {}", clause.to_string(heap))
        }
    }

    pub fn write_h(&self, heap: &Heap) {
        for (i,(c_type, clause)) in self.clauses.iter([false,false,false,false,true]){
            println!("{c_type:?}, {}", clause.to_string(heap))
        }
    }
}

// impl<'a> Index<usize> for Program {
//     type Output = (ClauseType,Clause<'a>);

//     fn index(&'a self, index: usize) -> &Self::Output {
//         self.clauses.get(index)
//     }
// }
