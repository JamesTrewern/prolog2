use crate::{
    binding::{Binding, BindingTraits},
    heap::Heap,
    state::State,
    unification::unify,
};
use std::{collections::HashMap, ops::Index, usize, vec};

use super::clause::{Clause, ClauseTraits};
pub type PredicateFN = fn(Box<[usize]>, &mut Heap) -> bool;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];
pub enum Predicate {
    FUNCTION(PredicateFN),
    CLAUSES(bool, Box<[usize]>), //allow match var, clause list
}
#[derive(Debug)]
pub struct Choice {
    clause: usize, // index in program clause bank
    pub binding: Binding,
    pub new_clause: bool,
}

impl Choice {
    pub fn choose(&mut self, state: &mut State) -> Vec<usize> {
        self.binding.undangle_const(&mut state.heap);
        self.build_goals(state)
    }
    pub fn build_goals(&mut self, state: &mut State) -> Vec<usize> {
        let mut goals: Vec<usize> = vec![];
        for body_literal in &state.prog.clauses[self.clause].1[1..] {
            goals.push(
                match self.binding.build_goal(*body_literal, &mut state.heap) {
                    Some(new_goal) => new_goal,
                    None => *body_literal,
                },
            );
        }
        goals
    }
    pub fn build_clause(&mut self, state: &mut State) ->Clause {
        self.binding.build_clause(&mut state.heap, &state.prog[self.clause])
    }
}

#[derive(PartialEq)]
enum ClauseType {
    CLAUSE,
    META,
    HYPOTHESIS,
}
pub struct Program {
    predicates: HashMap<(usize, usize), Predicate>, //(id, arity): Predicate
    clauses: Vec<(ClauseType, Clause)>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            predicates: HashMap::new(),
            clauses: vec![],
        }
    }
    pub fn add_module(&mut self, pred_module: PredModule, heap: &mut Heap) {
        for (symbol, arity, f) in pred_module {
            let id = heap.add_const_symbol(symbol);
            self.predicates
                .insert((id, *arity), Predicate::FUNCTION(*f));
        }
    }

    pub fn handle_directive(&mut self, directive: &str) {}

    fn match_clause(&self, clause: usize, goal_addr: usize, heap: &Heap) -> Option<Choice> {
        let (clause_type, literals) = &self.clauses[clause];
        if let Some(binding) = unify(literals[0], goal_addr, heap) {
            Some(Choice {
                clause,
                binding,
                new_clause: *clause_type == ClauseType::META,
            })
        } else {
            None
        }
    }

    fn match_predicate(
        &self,
        predicate: &Predicate,
        goal_addr: usize,
        heap: &mut Heap,
        choices: &mut Vec<Choice>,
    ) {
        match predicate {
            Predicate::FUNCTION(pred_fn) => {
                let n = heap[goal_addr].1;
                pred_fn((goal_addr + 1..goal_addr + n + 1).collect(), heap);
            }
            Predicate::CLAUSES(_, clauses) => {
                for i in clauses.iter() {
                    if let Some(choice) = self.match_clause(*i, goal_addr, heap) {
                        choices.push(choice)
                    }
                }
            }
        }
    }

    pub fn call(&mut self, goal_addr: usize, heap: &mut Heap) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];
        match self.predicates.get(&heap[goal_addr]) {
            Some(predicate) => self.match_predicate(predicate, goal_addr, heap, &mut choices),
            None => {
                if heap[goal_addr].0 < isize::MAX as usize {
                    //match body preds
                    for clauses in
                        self.predicates
                            .iter()
                            .filter_map(|(_, predicate)| match predicate {
                                Predicate::FUNCTION(_) => None,
                                Predicate::CLAUSES(body, clauses) => Some(clauses),
                            })
                    {
                        for i in clauses.iter() {
                            if let Some(choice) = self.match_clause(*i, goal_addr, heap) {
                                choices.push(choice)
                            }
                        }
                    }
                }
                //match hypothesis
                let mut i = self.clauses.len() - 1;
                while self.clauses[i].0 == ClauseType::HYPOTHESIS {
                    if let Some(choice) = self.match_clause(i, goal_addr, heap) {
                        choices.push(choice)
                    }
                    i -= 1;
                }
                //match var preds
                let arity = heap[goal_addr].1;
                if let Some(predicate) = self.predicates.get(&(Heap::REF, arity)) {
                    self.match_predicate(predicate, goal_addr, heap, &mut choices)
                }
            }
        }
        choices
    }

    pub fn add_clause(&mut self, clause: Clause, heap: &Heap) {
        let i = self.clauses.len();
        let clause_type = if clause.higher_order(heap) {
            ClauseType::META
        } else {
            ClauseType::CLAUSE
        };
        let mut k = heap[clause[0]];
        self.clauses.push((clause_type, clause)); //K = (symbol,arity)
                                                  //Collect all var symbols of same arity to same map value
        if k.0 < isize::MAX as usize {
            k.0 = Heap::REF
        }
        match self.predicates.get_mut(&k) {
            Some(pred) => match pred {
                Predicate::FUNCTION(_) => panic!("Can't redefine predicate with built in function"),
                Predicate::CLAUSES(_, clauses) => {
                    *clauses = [[i].as_slice(), &**clauses].concat().into();
                }
            },
            None => {
                self.predicates
                    .insert(k, Predicate::CLAUSES(false, Box::new([i])));
            }
        }
    }

    //Add clause, If invented predicate symbol return true
    pub fn add_h_clause(&mut self, clause: Clause, heap: &Heap) -> bool{
        let symbol = 
    }

    pub fn add_constraint(&mut self, clause: Clause, heap: &Heap) {}

    pub fn write_prog(&self, heap: &Heap) {
        self.clauses
            .iter()
            .filter(|(ct, _)| *ct != ClauseType::HYPOTHESIS)
            .map(|(_, c)| c.write_clause(heap));
    }

    pub fn write_h(&self, heap: &Heap) {
        self.clauses
            .iter()
            .filter(|(ct, _)| *ct == ClauseType::HYPOTHESIS)
            .map(|(_, c)| c.write_clause(heap));
    }
}

impl Index<usize> for Program {
    type Output = Clause;

    fn index(&self, index: usize) -> &Self::Output {
        &self.clauses[index].1
    }
}
