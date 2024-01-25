use std::fs;
use std::ops::AddAssign;

use crate::terms::Substitution;
use crate::{atoms::Atom, Clause};

const CONSTRAINT_CLAUSE: &str = "<c>";

#[derive(Debug)]
pub struct Choice {
    pub goals: Vec<Atom>,
    pub subs: Substitution,
    pub new_clause: Option<Clause>,
}
pub struct Program {
    pub clauses: Vec<Clause>,
    pub constraints: Vec<Clause>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            clauses: vec![],
            constraints: vec![],
        }
    }

    pub fn match_head_to_goal(
        &self,
        goal: &Atom,
        id_counter: &mut u32,
        contraints: bool,
    ) -> Vec<Choice> {
        let mut choices = vec![];
        for clause in &self.clauses {
            match clause.match_goal(goal, id_counter) {
                Some(subs) => {
                    if contraints {
                        let subbed_clause = clause.apply_sub(&subs.0);
                        //println!("Subbed C: {}", subbed_clause.to_string());
                        if self.constraints.iter().any(|c| if c.can_unfiy(&subbed_clause){
                            println!("Denied: {}", subbed_clause.to_string());
                            println!("Contraint: {}",c.to_string());
                            true
                        }else{
                            false
                        }) {
                            continue;
                        }
                    }
                    println!("Choiceed:  {}", clause.to_string());
                    let new_clause = match subs.1 {
                        Some(ho_sub) => Some(clause.apply_sub(&ho_sub)),
                        None => None,
                    };
                    choices.push(Choice {
                        goals: clause.body().apply_sub(&subs.0).atoms,
                        subs: subs.0,
                        new_clause,
                    })
                }
                None => (),
            }
        }
        return choices;
    }

    pub fn parse_file(&mut self, path: &str) {
        let file = fs::read_to_string(path).expect("Unable to read file");
        for clause in file.split('.') {
            if clause == "" {
                continue;
            };
            if clause.contains(CONSTRAINT_CLAUSE) {
                self.constraints
                    .push(Clause::parse_clause(clause.to_owned()))
            } else {
                self.clauses.push(Clause::parse_clause(clause.to_owned()))
            }
        }
    }

    pub fn write_prog(&self) {
        for clause in self.clauses.iter() {
            println!("{}", clause.to_string());
        }
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
