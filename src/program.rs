use std::collections::HashMap;

use crate::atoms::{Atom, AtomHandler};
use crate::clause::{Choice, Clause, ClauseHandler};
use crate::heap::{Heap, HeapHandler};
use crate::terms::{Substitution, Term};
use crate::Config;
pub type PredicateFN =
    Box<dyn Fn(&mut Config, &mut Heap, &mut Vec<(usize, usize)>, &mut Substitution, &Atom) -> bool>;

enum Predicate {
    CLAUSES(Vec<usize>),
    FUNCTION(PredicateFN),
}

pub struct Program {
    clauses: Vec<Clause>,
    ho_clauses: Vec<Clause>,
    hypothesis: Vec<Clause>,
    constraints: Vec<Clause>,
    predicates: HashMap<(usize, usize), Predicate>, // Map Symbol and arity to list of clause indicies
    body_predicates: Vec<(usize, usize)>,
    invented_predicates: usize,
}

impl Program {
    pub fn new() -> Program {
        Program {
            clauses: vec![],
            ho_clauses: vec![],
            hypothesis: vec![],
            predicates: HashMap::new(),
            body_predicates: vec![],
            invented_predicates: 0,
            constraints: vec![],
        }
    }

    pub fn add_clause(&mut self, clause: Clause, heap: &Heap) {
        if clause.higher_order(heap) {
            self.ho_clauses.push(clause);
        } else {
            if let Some(pred) = self
                .predicates
                .get_mut(&(clause.pred_symbol(), clause.arity()))
            {
                if let Predicate::CLAUSES(clause_ids) = pred {
                    self.clauses.push(clause);
                    clause_ids.push(self.clauses.len() - 1);
                } else {
                    panic!(
                        "Can not redifine {}/{}",
                        heap.get_term(clause.pred_symbol()).to_string(),
                        clause.arity()
                    );
                }
            } else {
                self.predicates.insert(
                    (clause.pred_symbol(), clause.arity()),
                    Predicate::CLAUSES(vec![self.clauses.len()]),
                );
                self.clauses.push(clause);
            }
        }
    }

    pub fn add_pred(&mut self, symbol: &str, arity: usize, heap: &mut Heap, f: PredicateFN) {
        let symbol = heap.new_term(Some(Term::Constant(symbol.into())));
        self.predicates
            .insert((symbol, arity), Predicate::FUNCTION(f));
    }

    fn call_clauses(&self, clause_ids: &Vec<usize>, goal: &Atom, heap: &mut Heap) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];
        for i in clause_ids {
            let clause = &self.clauses[*i];
            if let Some(choice) = self.clauses[*i].match_goal(goal, heap) {
                choices.push(choice);
            }
        }
        return choices;
    }

    fn call_pred_f(
        &mut self,
        config: &mut Config,
        heap: &mut Heap,
        goal: &Atom,
        f: &PredicateFN,
    ) -> Vec<Choice> {
        let mut bindings: Substitution = vec![];
        if f(config, heap, &mut self.body_predicates, &mut bindings, goal) {
            return vec![Choice {
                goals: vec![],
                bindings: vec![],
                new_clause: None,
            }];
        } else {
            return vec![];
        }
    }

    fn call_unkown_pred(&self, goal: &Atom, heap: &mut Heap, config: &Config) -> Vec<Choice> {
        let mut choices = vec![];
        if config.max_clause != self.hypothesis.len() {
            //match Meta
            for clause in &self.ho_clauses {
                if let Some(choice) = clause.match_goal(goal, heap) {
                    choices.push(choice)
                }
            }
        }
        //match H
        for clause in &self.hypothesis {
            if let Some(choice) = clause.match_goal(goal, heap) {
                //Do bindings allow current clause to be subsumed by contraints
                let subbed = clause.apply_sub(&choice.bindings);
                if !self
                    .constraints
                    .iter()
                    .any(|constraint| constraint.subsumes(&subbed, heap))
                {
                    choices.push(choice)
                }
            }
        }
        return choices;
    }

    fn call_var_pred(&self, goal: &Atom, heap: &mut Heap, config: &Config) -> Vec<Choice> {
        let mut choices = vec![];

        if config.max_clause != self.hypothesis.len()
            && config.max_invented != self.invented_predicates
        {
            for clause in &self.ho_clauses {
                if let Some(choice) = clause.match_goal(goal, heap) {
                    choices.push(choice)
                }
            }
        }

        //match with body_preds
        for (p, arity) in &self.body_predicates {
            if *arity == goal.len() - 1 {
                if let Some(Predicate::CLAUSES(clause_ids)) = self.predicates.get(&(*p, *arity)) {
                    for i in clause_ids {
                        let clause = &self.clauses[*i];
                        if let Some(choice) = clause.match_goal(goal, heap) {
                            // println!("body: {}, {:?", clause.to_string(heap), choice.bindings);
                            choices.push(choice)
                        }
                    }
                }
            }
        }

        //match H
        for clause in &self.hypothesis {
            if let Some(choice) = clause.match_goal(goal, heap) {
                //Do bindings allow current clause to be subsumed by contraints
                let subbed = clause.apply_sub(&choice.bindings);
                if !self
                    .constraints
                    .iter()
                    .any(|constraint| constraint.subsumes(&subbed, heap))
                {
                    choices.push(choice)
                }
            }
        }

        //If matching meta invent predicate symbol and substitution
        return choices;
    }

    pub fn call(&mut self, goal: &Atom, heap: &mut Heap, config: &mut Config) -> Vec<Choice> {
        if let Some(pred) = self.predicates.get(&(heap.deref(goal[0]), goal.len() - 1)) {
            match pred {
                Predicate::CLAUSES(clause_ids) => self.call_clauses(clause_ids, goal, heap),
                Predicate::FUNCTION(f) => {
                    let mut bindings: Substitution = vec![];
                    if f(config, heap, &mut self.body_predicates, &mut bindings, goal) {
                        return vec![Choice {
                            goals: vec![],
                            bindings,
                            new_clause: None,
                        }];
                    } else {
                        return vec![];
                    }
                }
            }
        } else {
            if heap.get_term(goal[0]).enum_type() == "Constant" {
                // println!("UK Pred");
                self.call_unkown_pred(goal, heap, config)
            } else {
                // println!("Var Pred");
                self.call_var_pred(goal, heap, config)
            }
        }
    }

    pub fn add_h_clause(&mut self, clause: Clause, heap: &mut Heap) -> Option<usize> {
        //If clause head is var invent pred symbol
        if heap.get_term(clause.pred_symbol()).enum_type() == "Ref" {
            self.invented_predicates += 1;
            println!(
                "New Clause: {}, Invented:{}, Clauses:{}",
                clause.to_string(heap),
                self.invented_predicates,
                self.hypothesis.len() + 1
            );
            self.hypothesis.push(clause);
            Some(heap.new_term(Some(Term::Number(self.invented_predicates as f64))))
        } else {
            println!(
                "New Clause: {}, Invented:{}, Clauses:{}",
                clause.to_string(heap),
                self.invented_predicates,
                self.hypothesis.len()
            );

            self.hypothesis.push(clause);
            None
        }
    }

    pub fn add_constraint(&mut self, clause: Clause) {
        self.constraints.push(clause)
    }

    pub fn remove_h_clause(&mut self, invented: bool) -> Option<Clause> {
        if invented {
            self.invented_predicates -= 1;
        }
        self.hypothesis.pop()
    }

    pub fn reset_h(&mut self) {
        self.hypothesis.clear();
    }

    pub fn write_prog(&self, heap: &Heap) {
        for clause in self.clauses.iter() {
            println!("{}", clause.to_string(heap));
        }
        for clause in self.ho_clauses.iter() {
            println!("{}", clause.to_string(heap));
        }
        print!("Body_Preds:[");
        for (symbol, arity) in &self.body_predicates {
            print!("{}/{arity},", heap.get_term(*symbol).to_string());
        }
        println!("]");
    }

    pub fn write_h(&self, heap: &Heap) {
        for clause in self.hypothesis.iter() {
            println!("{}", clause.to_string(heap));
        }
    }
}
