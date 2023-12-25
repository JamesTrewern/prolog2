use std::{
    collections::HashMap,
    ops::{self, AddAssign},
};

use crate::heap::Heap;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Term {
    Constant(Box<str>),
    REF(usize),      //Query Variable
    EQVar(Box<str>), //Existentialy Quantified Variable
    AQVar(Box<str>), //Universally Quantified Variable
}

impl Term {
    pub fn to_string(&self) -> String {
        match self {
            Term::Constant(symbol) => symbol.to_string(),
            Term::EQVar(symbol) => symbol.to_string(),
            Term::REF(id) => "_".to_string() + &id.to_string(),
            Term::AQVar(symbol) => "∀'".to_string() + &symbol.to_string(),
        }
    }
    pub fn unify<'a>(&'a self, other: &'a Term) -> Option<(&'a Term, &'a Term)> {
        if let &Term::Constant(value1) = &self {
            if let &Term::Constant(value2) = &other {
                if value1 != value2 {
                    return None;
                }
            }
        }
        let order1 = match self {
            Term::Constant(_) => 3,
            Term::REF(_) => 2,
            Term::EQVar(_) => 1,
            Term::AQVar(_) => 0,
        };
        let order2 = match other {
            Term::Constant(_) => {
                if order1 == 3 && self != other {
                    return None;
                } else {
                    3
                }
            }
            Term::REF(_) => 2,
            Term::EQVar(_) => 1,
            Term::AQVar(_) => 0,
        };
        match order1 < order2 {
            true => Some((self, other)),
            false => Some((other, self)),
        }
    }

    pub fn enum_type(&self) -> &str {
        match self {
            Term::Constant(_) => "Constant",
            Term::REF(_) => "Ref",
            Term::EQVar(_) => "EQVar",
            Term::AQVar(_) => "AQVar",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Substitution {
    pub subs: HashMap<usize, usize>,
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution {
            subs: HashMap::new(),
        }
    }

    pub fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::from("{");
        for (k, v) in self.subs.iter() {
            let k = heap.get_term(*k);
            let v = heap.get_term(*v);
            buf += &k.to_string();
            buf += "/";
            buf += &v.to_string();
            buf += ", ";
        }
        buf.pop();
        buf += "}";
        return buf;
    }

    pub fn compound_sub(&self, k: usize) -> usize {
        match self.subs.get(&k) {
            Some(v) => self.compound_sub(*v),
            None => k.clone(),
        }
    }

    pub fn simplify(&mut self) {
        let mut new_subs: HashMap<usize, usize> = HashMap::new();
        //For all values update with compound_sub
        for k in self.subs.keys() {
            new_subs.insert(k.clone(), self.compound_sub(*k));
        }
        self.subs = new_subs;
    }

    pub fn universal_quantification(&self, heap: &mut Heap) -> Substitution {
        let mut ho_sub = Substitution::new();
        for (i1, i2) in &self.subs {
            let t1 = heap.get_term(*i1);
            match t1 {
                Term::AQVar(symbol) => {
                    let i3 = heap.new_term(Some(Term::EQVar(symbol.clone())));
                    ho_sub.subs.insert(*i1, i3);
                },
                _ => {
                    ho_sub.subs.insert(*i1, *i2);
                },
            };
        }
        return ho_sub;
    }

    pub fn unify(&mut self, other: Substitution, heap: &Heap) -> Option<Substitution> {
        let mut new_sub = self.clone();
        for (k, v1) in other.subs {
            match self.subs.get(&k) {
                Some(v2) => {
                    match heap.unify(v1,*v2) {
                        Some((t1, t2)) => new_sub.subs.insert(k, t2),
                        None => return None,
                    };
                }
                None => {
                    new_sub.subs.insert(k, v1);
                }
            };
        }
        return Some(new_sub);
    }

    pub fn filter(&mut self, heap: &Heap) {
        let mut key_to_remove = vec![];
        for key in self.subs.keys() {
            match heap[*key] {
                Term::REF(_) => (),
                _ => {
                    key_to_remove.push(key.clone());
                }
            }
        }
        for key in key_to_remove {
            self.subs.remove(&key);
        }
    }
}

impl ops::Add<Substitution> for Substitution {
    type Output = Substitution;

    fn add(self, rhs: Substitution) -> Substitution {
        let mut res = Substitution::new();
        for (k, v) in self.subs.iter() {
            res.subs.insert(*k, *v);
        }
        for (k, v) in rhs.subs.iter() {
            res.subs.insert(*k, *v);
        }
        res.simplify();
        return res;
    }
}

impl AddAssign<Substitution> for Substitution {
    fn add_assign(&mut self, rhs: Substitution) {
        for (k, v) in rhs.subs {
            self.subs.insert(k, v);
        }
    }
}
