use crate::terms::{Substitution, Term};
use core::fmt;
use std::collections::HashSet;
#[derive(Clone, Debug)]
pub struct Atom {
    pub terms: Vec<Term>,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Atom {
    pub fn to_string(&self) -> String {
        let mut buf = String::new();
        buf += &self.terms[0].to_string();
        buf += "(";
        for term in &self.terms[1..] {
            buf += &term.to_string();
            buf += ",";
        }
        buf.pop();
        buf += ")";
        return buf;
    }

    pub fn parse(atom_str: &str) -> Atom {
        let i1 = match atom_str.find("(") {
            Some(i) => i,
            None => 0,
        };
        let i2 = match atom_str.find(")") {
            Some(i) => i,
            None => 0,
        };

        let mut terms: Vec<Term> = vec![];

        let predicate_string = atom_str[0..i1].to_string();
        if predicate_string.chars().next().unwrap().is_uppercase(){
            terms.push(Term::EQVar(atom_str[0..i1].to_string()));
        }else{
            terms.push(Term::Constant(atom_str[0..i1].to_string()));
        }
        
        let args = &atom_str[(i1 + 1)..i2];

        for term_string in args.split(',') {
            if term_string.chars().next().unwrap().is_uppercase() {
                terms.push(Term::EQVar(term_string.to_string()));
            } else {
                terms.push(Term::Constant(term_string.to_string()));
            };
        }
        Atom { terms }
    }

    pub fn unify<'a>(&'a self, other: &'a Atom) -> Option<Substitution> {
        if self.terms.len() != other.terms.len() {
            return None;
        }
        let mut substitution: Substitution = Substitution::new();
        for i in 0..self.terms.len() {
            match self.terms[i].unify(&other.terms[i]) {
                Some((t1, t2)) => match t1 {
                    Term::Constant(_) => (),
                    _ => match substitution.get(t1) {
                        Some(v) => {
                            if *v != *t2 {
                                match v.unify(t2) {
                                    Some((t3, t4)) => {
                                        substitution.insert(t3.clone(), t4.clone());
                                    }
                                    None => return None,
                                }
                            }
                        }
                        None => {
                            substitution.insert(t1.clone(), t2.clone());
                        }
                    },
                },
                None => return None,
            };
        }
        return Some(substitution);
    }

    pub fn apply_subs(&self, sub: &Substitution) -> Atom {
        let mut new_atom: Atom = Atom { terms: vec![] };
        for term in &self.terms {
            match sub.get(&term) {
                Some(sub_term) => new_atom.terms.push(sub_term.clone()),
                None => new_atom.terms.push(term.clone()),
            }
        }
        return new_atom;
    }

    pub fn eq_vars(&self) -> Vec<Term> {
        self.terms
            .clone()
            .into_iter()
            .filter(|t| match t {
                Term::EQVar(_) => true,
                _ => false,
            })
            .collect()
    }

    pub fn eqvars_to_quvars(&mut self, id_counter: &mut u32) {
        let mut eq_vars: HashSet<Term> = HashSet::new();
        for var in self.eq_vars() {
            eq_vars.insert(var);
        }
        let mut subs = Substitution::new();
        for eq_var in eq_vars {
            subs.insert(eq_var, Term::QUVar(*id_counter));
            *id_counter += 1;
        }
        *self = self.apply_subs(&subs);
    }
}

impl PartialEq for Atom{
    fn eq(&self, other: &Self) -> bool {
        self.terms == other.terms
    }
}