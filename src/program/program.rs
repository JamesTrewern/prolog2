use crate::{
    heap::Heap,
    state::Config,
    unification::*,
};
use super::{
    choice::Choice,
    clause::*,
    clause_table::ClauseTable
};
use std::collections::HashMap;

const PRED_NAME: &'static str = "James";

pub type PredicateFN = fn(Box<[usize]>, &mut Heap) -> bool;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];

pub struct Program {
    predicate_functions: HashMap<(usize, usize), PredicateFN>,
    pub predicates: HashMap<(usize, usize), Vec<usize>>, //(id, arity): Predicate
    pub clauses: ClauseTable,
    pub constraints: Vec<(usize,usize)>,
    invented_preds: usize,
    pub h_size: usize,
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
            if clause_type != ClauseType::CLAUSE {
                if self.check_constraints(&binding, heap){
                    return None;
                }
            }
            Some(Choice {
                clause: clause_i,
                binding,
                new_clause: clause_type == ClauseType::META,
                check_contraint: clause_type == ClauseType::HYPOTHESIS,
            })
        } else {
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
            println!("{clauses:?}");
            for i in clauses.iter() {
                if let Some(choice) = self.match_clause(*i, goal_addr, heap) {
                    choices.push(choice)
                }
            }
        } else {
            let iterator = if symbol < Heap::CON_PTR {
                self.clauses.iter([false, false, true, true, true])
            } else {
                self.clauses.iter([false, false, false, true, true])
            };
            //TO DO use clause returned by iterator
            for (i, _) in iterator {
                if let Some(choice) = self.match_clause(i, goal_addr, heap) {
                    choices.push(choice);
                }
            }
        }
        choices
    }

    pub fn add_clause(&mut self, clause_type: ClauseType, clause: Box<Clause>) {
        self.clauses.add_clause(clause, clause_type);
    }

    //Add clause, If invented predicate symbol return true
    pub fn add_h_clause(
        &mut self,
        clause: Box<Clause>,
        heap: &mut Heap,
        config: &Config,
    ) -> Option<Option<usize>> {
        if self.h_size == config.max_clause {
            println!("Max H size can't add clause");
            clause.deallocate(heap);
            return None;
        }
        let symbol = clause.pred_symbol(heap);

        let id = if symbol < Heap::CON_PTR {
            if self.invented_preds == config.max_invented {
                println!("Max invented predicates can't add clause");
                clause.deallocate(heap);
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

        for atom1 in clause.iter(){
            for atom2 in clause.iter(){
                if atom1 == atom2 {continue;}
                if heap[*atom1].1 == heap[*atom2].1 && heap[atom1+1] != heap[atom2+1]{
                    self.constraints.push((atom1+1,atom2+1));
                    self.constraints.push((atom2+1,atom1+1));
                }
            }
        }

        self.clauses.add_clause(clause, ClauseType::HYPOTHESIS);
        self.h_size += 1;

        Some(id)
    }

    pub fn remove_h_clause(&mut self, invented: bool) {
        self.h_size -= 1;
        if invented {
            self.invented_preds -= 1;
        }
        self.clauses.remove_clause(self.clauses.clauses.len() - 1)
    }

    pub fn check_constraints(&self, binding: &Binding, heap: &Heap) -> bool {
        binding.iter().any(|b| self.constraints.contains(b))
    }

    pub fn write_prog(&self, heap: &Heap) {
        for (i, (c_type, clause)) in self.clauses.iter([true, true, true, true, false]) {
            println!("{c_type:?}, {}", clause.to_string(heap))
        }
    }

    pub fn write_h(&self, heap: &Heap) {
        for (i, (c_type, clause)) in self.clauses.iter([false, false, false, false, true]) {
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
