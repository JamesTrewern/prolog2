use std::fs;
use std::ops::AddAssign;

use crate::terms::{Substitution, Term};
use crate::{atoms::Atom, clause::Clause};

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
        heap: &mut Vec<Term>,
        contraints: bool,
    ) -> Vec<Choice> {
        let mut choices = vec![];
        for clause in &self.clauses {
            match clause.atoms[0].unify(goal) {
                Some(mut subs) => {
                    //unmapped EQ to new QU
                    let ids = subs.unmapped_to_qu(clause.unmapped_vars(&subs), heap.len()-1);
                    for id in ids{
                        heap.insert(id, Term::QUVar(id));
                    }

                    let mut goals_clause = clause.body().apply_sub(&subs);

                    let mut new_clause = None;
                    if clause.higher_order(){
                        let ho_subs = subs.universal_quantification();
                        new_clause = Some(clause.apply_sub(&ho_subs));
                    }
                    choices.push(Choice { goals: goals_clause.atoms, subs, new_clause })
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
