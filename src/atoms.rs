use crate::{
    heap::Heap,
    terms::{Substitution, Term},
};
#[derive(Clone, Debug)]
pub struct Atom {
    pub terms: Vec<usize>,
}

impl Atom {
    pub fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::new();
        buf += &heap.get_term(self.terms[0]).to_string();
        buf += "(";
        for term in &self.terms[1..] {
            buf += &heap.get_term(*term).to_string();
            buf += ",";
        }
        buf.pop();
        buf += ")";
        return buf;
    }

    pub fn parse(atom_str: &str, heap: &mut Heap, aqvars: Option<&Vec<&str>>) -> Atom {
        let binding = vec![];
        let aqvars = match aqvars {
            Some(v) => v,
            None => &binding,
        };
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
        if predicate_string.chars().next().unwrap().is_uppercase() {
            terms.push(Term::EQVar(atom_str[0..i1].into()));
        } else {
            terms.push(Term::Constant(atom_str[0..i1].into()));
        }

        let args = &atom_str[(i1 + 1)..i2];

        for term_string in args.split(',') {
            if term_string.chars().next().unwrap().is_uppercase() {
                if aqvars.contains(&term_string) {
                    terms.push(Term::AQVar(term_string.into()));
                } else {
                    terms.push(Term::EQVar(term_string.into()));
                }
            } else {
                terms.push(Term::Constant(term_string.into()));
            };
        }
        Atom {
            terms: terms.into_iter().map(|t| heap.new_term(Some(t))).collect(),
        }
    }

    pub fn unify(&self, other: &Atom, heap: &mut Heap) -> Option<Substitution> {
        if self.terms.len() != other.terms.len() {
            return None;
        }
        let mut substitution: Substitution = Substitution::new();
        for i in 0..self.terms.len() {
            match heap.unify(self.terms[i], other.terms[i]) {
                Some((i1, i2)) => {
                    if heap.get_term(i1).enum_type() != "Constant" {
                        match substitution.subs.get(&i1) {
                            Some(i3) => {
                                if *i3 != i2 {
                                    match heap.unify(*i3, i2) {
                                        Some((t3, t4)) => {
                                            substitution.subs.insert(t3, t4);
                                        }
                                        None => return None,
                                    }
                                }
                            }
                            None => {
                                substitution.subs.insert(i1, i2);
                            }
                        }
                    }
                }
                None => return None,
            };
        }
        return Some(substitution);
    }

    pub fn apply_subs(&self, sub: &Substitution) -> Atom {
        let mut new_atom: Atom = Atom { terms: vec![] };
        for i1 in &self.terms {
            match sub.subs.get(&i1) {
                Some(i2) => new_atom.terms.push(*i2),
                None => new_atom.terms.push(*i1),
            }
        }
        return new_atom;
    }

    pub fn eq_to_ref(&mut self, heap: &mut Heap){
        for i in 0..self.terms.len(){
            if heap.get_term(self.terms[i]).enum_type() == "EQVar"{
                self.terms[i] = heap.new_term(None);
            }
        }
    }
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        self.terms == other.terms
    }
}
