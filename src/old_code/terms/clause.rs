use std::collections::HashSet;
use super::{
    heap::Heap,
    substitution::{Substitution,SubstitutionHandler},
    atoms::{Atom, AtomHandler},
    terms::Term,
};
const CLAUSE: &str = ":-";
#[derive(Debug)]
pub struct Choice {
    pub goals: Clause,
    pub bindings: Substitution,
    pub new_clause: Option<Clause>,
}

pub type Clause = Vec<Atom>;

pub trait ClauseHandler {
    fn eq_to_ref(&mut self, heap: &mut Heap);
    fn subsumes(&self, other: &Clause, heap: &mut Heap) -> bool;
    fn arity(&self) -> usize;
    fn pred_symbol(&self) -> usize;
    fn aq_to_eq(&mut self, heap: &mut Heap);
    fn higher_order(&self, heap: &Heap) -> bool;
    fn body(&self) -> Clause;
    fn parse_clause(string: &str, heap: &mut Heap) -> Clause;
    fn match_goal(&self, goal: &Atom, heap: &mut Heap) -> Option<Choice>;
    fn apply_sub(&self, subs: &Substitution) -> Clause;
    fn terms(&self) -> HashSet<usize>;
    fn to_string(&self, heap: &Heap) -> String;
}

impl ClauseHandler for Clause {
    fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::new();
        if self.len() == 1 {
            buf += &(self[0].to_string(heap));
            buf += ".";
        } else {
            buf += &(self[0].to_string(heap));
            buf += " <-- ";
            for atom in &self[1..] {
                buf += &atom.to_string(heap);
                buf += ", "
            }
        }
        return buf;
    }

    fn terms(&self) -> HashSet<usize> {
        let mut terms: HashSet<usize> = HashSet::new();
        for atom in self {
            for term in atom {
                terms.insert(*term);
            }
        }
        return terms;
    }

    fn apply_sub(&self, subs: &Substitution) -> Clause {
        let mut new_atoms: Vec<Atom> = vec![];
        for atom in self {
            new_atoms.push(atom.apply_subs(&subs));
        }
        return new_atoms;
    }

    fn match_goal(&self, goal: &Atom, heap: &mut Heap) -> Option<Choice> {
        let head = &self[0];
        let bindings: Substitution;
        // Get subs to create goal clause
        if head.len() != goal.len() {
            return None;
        }
        if let Some(subs) = head.unify(goal, heap) {
            //Get bindings
            bindings = subs.bindings(heap);
            //Produce Goals with subs
            let goals = self.body().apply_sub(&subs);
            //If new clause, produce new clause by only subbing EQs + new_clause.aq_to_eq
            let mut new_clause = None;
            if self.higher_order(heap) {
                new_clause = Some(self.apply_sub(&subs.meta(heap)));
            }
            Some(Choice {
                goals,
                bindings,
                new_clause,
            })
        } else {
            None
        }
    }

    fn parse_clause(string: &str, heap: &mut Heap) -> Clause {
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
            atoms.push(Atom::parse(&clause_string, heap, &aqvars));
            return atoms;
        }

        let i1 = clause_string.find(CLAUSE).unwrap();
        let i2 = i1 + CLAUSE.len();

        atoms.push(Atom::parse(&clause_string[..i1], heap, &aqvars));
        let mut buf: String = String::new();
        let mut in_brackets = 0;
        for char in clause_string[i2..].chars() {
            match char {
                ',' => {
                    if in_brackets == 0 {
                        atoms.push(Atom::parse(&buf, heap, &aqvars));
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
        atoms.push(Atom::parse(&buf, heap, &aqvars));
        return atoms;
    }

    fn body(&self) -> Clause {
        let atoms: Vec<Atom> = self[1..].to_vec();
        return atoms;
    }

    fn higher_order(&self, heap: &Heap) -> bool {
        self.iter().any(|a| match heap.get_term(a[0]) {
            Term::EQVar(_) => true,
            Term::AQVar(_) => true,
            _ => false,
        })
    }

    fn subsumes(&self, other: &Clause, heap: &mut Heap) -> bool {
        // if let Some(mut subs) = self[0].unify(&other[0], heap){
        //     //Does subs applied to self result in subset of body of other
        //     let subbed = self.apply_sub(&subs);
        //     //For each I in body does self[i] = other[i]
        // }
        if self.len() != other.len() {
            return false;
        }
        let mut cumalitve_subs = Substitution::new();
        for i in 0..self.len() {
            let subs = match self[i].unify(other.get(i).unwrap(), heap) {
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

    fn aq_to_eq(&mut self, heap: &mut Heap) {
        let mut terms = self.terms();
        terms.retain(|a| heap[*a].enum_type() == "AQVar");
        let subs: Substitution = terms
            .iter()
            .map(|a| {
                if let Term::AQVar(value) = heap.get_term(*a) {
                    let term = Term::EQVar(value.clone());
                    (*a, heap.new_term(Some(term)))
                } else {
                    panic!("Retain didn't work")
                }
            })
            .collect();
        *self = self.apply_sub(&subs);
        // println!("{}", self.to_string(heap));
    }

    fn eq_to_ref(&mut self, heap: &mut Heap) {
        println!("{}", self.to_string(heap));
        let mut terms = self.terms();
        terms.retain(|a| heap[*a].enum_type() == "EQVar");
        let subs: Substitution = terms.iter().map(|a| (*a, heap.new_term(None))).collect();
        *self = self.apply_sub(&subs);
        // println!("{}", self.to_string(heap));
    }

    fn pred_symbol(&self) -> usize {
        self[0][0]
    }

    fn arity(&self) -> usize {
        self[0].len() - 1
    }
}
