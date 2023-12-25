use std::collections::HashSet;

use crate::atoms::Atom;
use crate::heap::Heap;
use crate::terms::{Substitution, Term};

const CLAUSE: &str = ":-";

#[derive(Clone, Debug)]
pub struct Clause {
    pub atoms: Vec<Atom>,
}

impl Clause {
    pub fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::new();
        if self.atoms.len() == 1 {
            buf += &(self.atoms[0].to_string(heap));
            buf += ".";
        } else {
            buf += &(self.atoms[0].to_string(heap));
            buf += " <-- ";
            for atom in &self.atoms[1..] {
                buf += &atom.to_string(heap);
                buf += ", "
            }
        }
        return buf;
    }

    pub fn new(atoms: Vec<Atom>) -> Clause {
        return Clause { atoms };
    }

    pub fn terms(&self) -> HashSet<usize> {
        let mut terms: HashSet<usize> = HashSet::new();
        for atom in &self.atoms {
            for term in &atom.terms {
                terms.insert(*term);
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

    pub fn parse_clause(string: &str, heap: &mut Heap) -> Clause {
        let mut clause_string = string.to_string();
        clause_string.retain(|c| !c.is_whitespace());
        let mut aqvars: Vec<&str> = vec![];
        let mut split = clause_string.split('\\');
        let clause_string = split.next().unwrap().to_string();
        match split.next() {
            Some(symbols) => {
                for symbol in symbols.split(',') {
                    aqvars.push(symbol);
                }
            }
            None => (),
        };

        // clause_string.retain(|c| !c.is_whitespace());
        let mut atoms: Vec<Atom> = vec![];
        if !clause_string.contains(CLAUSE) {
            atoms.push(Atom::parse(&clause_string, heap, Some(&aqvars)));
            return Clause::new(atoms);
        }

        let i1 = clause_string.find(CLAUSE).unwrap();
        let i2 = i1 + CLAUSE.len();

        atoms.push(Atom::parse(&clause_string[..i1], heap, Some(&aqvars)));
        let mut buf: String = String::new();
        let mut in_brackets = 0;
        for char in clause_string[i2..].chars() {
            match char {
                ',' => {
                    if in_brackets == 0 {
                        atoms.push(Atom::parse(&buf, heap, Some(&aqvars)));
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
        atoms.push(Atom::parse(&buf, heap, Some(&aqvars)));
        return Clause::new(atoms);
    }

    pub fn body(&self) -> Clause {
        let atoms: Vec<Atom> = self.atoms[1..].to_vec();
        return Clause { atoms };
    }

    pub fn higher_order(&self, heap: &Heap) -> bool {
        self.atoms.iter().any(|a| match heap.get_term(a.terms[0]) {
            Term::EQVar(_) => true,
            Term::AQVar(_) => true,
            _ => false,
        })
    }

    pub fn can_unfiy(&self, other: &Clause, heap: &mut Heap) -> bool {
        if self.atoms.len() != other.atoms.len() {
            return false;
        }
        let mut cumalitve_subs = Substitution::new();
        for i in 0..self.atoms.len() {
            let subs = match self
                .atoms
                .get(i)
                .unwrap()
                .unify(other.atoms.get(i).unwrap(), heap)
            {
                Some(s) => s,
                None => return false,
            };
            // println!("subs: {}", subs.to_string());
            cumalitve_subs = match cumalitve_subs.unify(subs, heap) {
                Some(v) => v,
                None => {
                    return false;
                }
            }
        }
        // println!("{}", cumalitve_subs.to_string());
        return true;
    }

    pub fn aq_to_eq(&mut self, heap: &mut Heap) {
        for i in 0..self.atoms.len() {
            for j in 0..self.atoms[i].terms.len() {
                match heap.get_term(self.atoms[i].terms[j]) {
                    Term::AQVar(symbol) => {
                        self.atoms[i].terms[j] = heap.new_term(Some(Term::EQVar(symbol.clone())));
                    }
                    _ => (),
                }
            }
        }
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
