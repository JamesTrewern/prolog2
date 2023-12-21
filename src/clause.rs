use std::collections::HashSet;

use crate::atoms::Atom;
use crate::terms::{Substitution, Term};

const CLAUSE: &str = ":-";

#[derive(Clone, Debug)]
pub struct Clause {
    pub atoms: Vec<Atom>,
}

impl Clause {
    pub fn to_string(&self) -> String {
        let mut buf = String::new();
        if self.atoms.len() == 1 {
            buf += &(self.atoms[0].to_string());
            buf += ".";
        } else {
            buf += &(self.atoms[0].to_string());
            buf += " <-- ";
            for atom in &self.atoms[1..] {
                buf += &atom.to_string();
                buf += ", "
            }
        }
        return buf;
    }

    pub fn new(atoms: Vec<Atom>) -> Clause {
        return Clause { atoms };
    }

    pub fn unmapped_vars(&self, subs: &Substitution) -> Vec<&Term> {
        let mut res: Vec<&Term> = vec![];
        for term in self.terms() {
            if !subs.subs.contains_key(&term) && term.enum_type() != "Constant" {
                res.push(term);
            }
        }
        return res;
    }

    fn terms(&self) -> HashSet<&Term> {
        let mut terms: HashSet<&Term> = HashSet::new();
        for atom in &self.atoms {
            for term in &atom.terms {
                terms.insert(term);
            }
        }
        return terms;
    }

    pub fn apply_sub(&self, subs: &Substitution) -> Clause {
        let mut new_atoms: Vec<Atom> = vec![];
        for atom in &self.atoms {
            new_atoms.push(atom.apply_subs(&subs));
        }
        return Clause::new(new_atoms);
    }

    pub fn parse_clause(mut clause_string: String) -> Clause {
        clause_string.retain(|c| !c.is_whitespace());
        let mut aqvars = Substitution::new();
        match clause_string.find('\\') {
            Some(i) => {
                for symbol in clause_string[(i + 1)..].split(',') {
                    aqvars.insert(
                        Term::EQVar(symbol.into()),
                        Term::AQVar(symbol.into()),
                    );
                }
                clause_string.truncate(i);
            }
            None => (),
        };

        // clause_string.retain(|c| !c.is_whitespace());
        let mut atoms: Vec<Atom> = vec![];
        if !clause_string.contains(CLAUSE) {
            atoms.push(Atom::parse(&clause_string));
            return Clause::new(atoms);
        }

        let i1 = clause_string.find(CLAUSE).unwrap();
        let i2 = i1 + CLAUSE.len();

        atoms.push(Atom::parse(&clause_string[..i1]));
        let mut buf: String = String::new();
        let mut in_brackets = 0;
        for char in clause_string[i2..].chars() {
            match char {
                ',' => {
                    if in_brackets == 0 {
                        atoms.push(Atom::parse(&buf));
                        buf = String::new();
                        continue;
                    }
                }
                ')' => in_brackets -= 1,
                '(' => in_brackets += 1,
                _ => (),
            }
            buf.push(char);
        }
        atoms.push(Atom::parse(&buf));
        return Clause::new(atoms).apply_sub(&aqvars);
    }

    pub fn body(&self) -> Clause {
        //TO DO don't clone whole clause, just body from slice
        let mut atoms:Vec<Atom> = self.atoms[1..].to_vec();
        return Clause{atoms};
        // let mut body = self.clone();
        // body.atoms.remove(0);
        // return body;
    }

    pub fn higher_order(&self) -> bool {
        self.atoms.iter().any(|a| match a.terms.get(0).unwrap() {
            Term::EQVar(_) => true,
            Term::AQVar(_) => true,
            _ => false,
        })
    }

    pub fn can_unfiy(&self, other: &Clause) -> bool {
        if self.atoms.len() != other.atoms.len() {
            return false;
        }
        let mut cumalitve_subs = Substitution::new();
        for i in 0..self.atoms.len() {
            let subs = match self
                .atoms
                .get(i)
                .unwrap()
                .unify(other.atoms.get(i).unwrap())
            {
                Some(s) => s,
                None => return false,
            };
            // println!("subs: {}", subs.to_string());
            cumalitve_subs = match cumalitve_subs.unify(subs) {
                Some(v) => v,
                None => {
                    return false;
                }
            }
        }
        // println!("{}", cumalitve_subs.to_string());
        return true;
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        if self.atoms.len() != other.atoms.len() {
            return false;
        }
        for i in 0..self.atoms.len() {
            if self.atoms.get(i).unwrap() != other.atoms.get(i).unwrap() {
                return false;
            }
        }
        return true;
    }
}
