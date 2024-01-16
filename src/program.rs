use std::collections::HashSet;
use std::fs;
use std::ops::AddAssign;

use crate::heap::{self, Heap};
use crate::terms::{Substitution, Term};
use crate::{atoms::Atom, clause::Clause};

const CONSTRAINT_CLAUSE: &str = "<c>";

#[derive(Debug)]
pub struct Choice {
    pub goals: Vec<Atom>,
    pub subs: Substitution,
    pub new_clause: Option<Clause>,
}

impl Choice {
    pub fn choose(&mut self, heap: &mut Heap) {
        self.var_to_heap(heap);
        self.aq_to_eq(heap);
    }

    fn var_to_heap(&mut self, heap: &mut Heap) {
        let mut terms: HashSet<usize> = HashSet::new();
        for goal in self.goals.iter() {
            for term in goal.terms.iter() {
                if heap.get_term(*term).enum_type() == "EQVar" {
                    terms.insert(*term);
                }
            }
        }

        let mut subs = Substitution::new();
        for term in terms {
            subs.subs.insert(term, heap.new_term(None));
        }
        for i in 0..self.goals.len() {
            self.goals[i] = self.goals[i].apply_subs(&subs);
        }
        if let Some(clause) = &mut self.new_clause {
            *clause = clause.apply_sub(&subs);
        }
        let mut terms: HashSet<usize> = HashSet::new();
        for goal in self.goals.iter() {
            for term in goal.terms.iter() {
                if heap.get_term(*term).enum_type() == "AQVar" {
                    terms.insert(*term);
                }
            }
        }
        for term in terms {
            subs.subs.insert(term, heap.new_term(None));
        }
        for i in 0..self.goals.len() {
            self.goals[i] = self.goals[i].apply_subs(&subs);
        }
    }

    fn aq_to_eq(&mut self, heap: &mut Heap) {
        //To Do. some AQ needs to go in Ref in goals
        if let Some(clause) = &mut self.new_clause {
            clause.aq_to_eq(heap);
        }
    }
}
pub struct Program {
    pub clauses: Vec<Clause>,
    pub constraints: Vec<Clause>,
    pub predicate_symbols: HashSet<usize>
}

impl Program {
    pub fn new() -> Program {
        Program {
            clauses: vec![],
            constraints: vec![],
            predicate_symbols: HashSet::new(),
        }
    }

    pub fn match_head_to_goal(
        &self,
        goal: &Atom,
        heap: &mut Heap,
        contraints: bool,
    ) -> Vec<Choice> {
        let mut choices = vec![];
        for clause in &self.clauses {
            match clause.atoms[0].unify(goal, heap) {
                Some(subs) => {
                    // println!(
                    //     "Matched: {}\nSubs:   {}",
                    //     clause.to_string(heap),
                    //     subs.to_string(heap)
                    // );
                    let goals_clause = clause.body().apply_sub(&subs);

                    let mut new_clause = None;
                    if clause.higher_order(heap) {
                        let ho_subs = subs.universal_quantification(heap);
                        new_clause = Some(clause.apply_sub(&ho_subs));
                    }
                    choices.push(Choice {
                        goals: goals_clause.atoms,
                        subs,
                        new_clause,
                    })
                }
                None => (),
            }
        }
        return choices;
    }

    pub fn parse_file(&mut self, path: &str, heap: &mut Heap) {
        let file = fs::read_to_string(path)
            .expect("Unable to read file")
            .trim()
            .to_string();
        for clause in file.split('.') {
            if clause == "" {
                continue;
            };
            if clause.contains(CONSTRAINT_CLAUSE) {
                self.constraints.push(Clause::parse_clause(clause, heap))
            } else {
                self.clauses.push(Clause::parse_clause(clause, heap))
            }
        }
        self.predicate_symbols = self.predicate_symbols();
    }

    pub fn write_prog(&self, heap: &Heap) {
        for clause in self.clauses.iter() {
            println!("{}", clause.to_string(heap));
        }
    }

    //TO DO store these values 
    pub fn predicate_symbols(&self) -> HashSet<usize>{
        let mut symbols = HashSet::new();
        for clause in &self.clauses{
            symbols.insert(clause.atoms[0].terms[0]);
        }
        return symbols;
    }
}

impl AddAssign<Clause> for Program {
    fn add_assign(&mut self, rhs: Clause) {
        self.clauses.push(rhs)
    }
}

impl AddAssign<Vec<Clause>> for Program {
    fn add_assign(&mut self, mut rhs: Vec<Clause>) {
        self.clauses.append(&mut rhs);
    }
}
