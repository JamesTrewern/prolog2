use crate::{
    heap::{Heap, HeapHandler},
    terms::{Substitution, SubstitutionHandler, Term},
};

pub type Atom = Vec<usize>;

pub trait AtomHandler {
    fn to_string(&self, heap: &Heap) -> String;
    fn parse(atom_str: &str, heap: &mut Heap, aqvars: Option<&Vec<&str>>) -> Self;
    fn unify(&self, other: &Atom, heap: &Heap) -> Option<Substitution>;
    fn apply_subs(&self, sub: &Substitution) -> Atom;
    fn eq_to_ref(&mut self, heap: &mut Heap);
    fn var_pred(&self, heap: &Heap) -> bool;
}

impl AtomHandler for Atom {
    fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::new();
        buf += &heap.get_term(self[0]).to_string();
        buf += "(";
        for term in &self[1..] {
            buf += &heap.get_term(*term).to_string();
            buf += ",";
        }
        buf.pop();
        buf += ")";
        return buf;
    }

    fn parse(atom_str: &str, heap: &mut Heap, aqvars: Option<&Vec<&str>>) -> Atom {
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
        } else if let Ok(value) = predicate_string.parse::<f64>() {
            terms.push(Term::Number(value))
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
            } else if let Ok(value) = term_string.trim().parse::<f64>() {
                terms.push(Term::Number(value))
            } else {
                terms.push(Term::Constant(term_string.into()));
            };
        }
        terms.into_iter().map(|t| heap.new_term(Some(t))).collect()
    }

    // find substitution from self to other
    fn unify(&self, other: &Atom, heap: &Heap) -> Option<Substitution> {
        if self.len() != other.len() {
            return None;
        }
        let mut substitution: Substitution = Substitution::new();
        for i in 0..self.len() {
            match heap.unify(self[i], other[i]) {
                Some((i1, i2)) => {
                    if heap.get_term(i1).enum_type() != "Constant" {
                        match substitution.get_sub(i1) {
                            Some(i3) => {
                                if i3 != i2 {
                                    match heap.unify(i3, i2) {
                                        Some((t3, t4)) => {
                                            substitution.insert_sub(t3, t4);
                                        }
                                        None => return None,
                                    }
                                }
                            }
                            None => {
                                substitution.insert_sub(i1, i2);
                            }
                        }
                    }
                }
                None => return None,
            };
        }
        return Some(substitution);
    }

    fn apply_subs(&self, sub: &Substitution) -> Atom {
        let mut new_atom: Atom = vec![];
        for i1 in self {
            match sub.get_sub(*i1) {
                Some(i2) => new_atom.push(i2),
                None => new_atom.push(*i1),
            }
        }
        return new_atom;
    }

    fn eq_to_ref(&mut self, heap: &mut Heap) {
        for i in 0..self.len() {
            if heap.get_term(self[i]).enum_type() == "EQVar" {
                self[i] = heap.new_term(None);
            }
        }
    }

    fn var_pred(&self, heap: &Heap) -> bool {
        heap.get_term(self[0]).enum_type() != "Constant"
    }
}
