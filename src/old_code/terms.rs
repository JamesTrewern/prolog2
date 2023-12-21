use std::{
    collections::HashMap,
    ops::{self, AddAssign},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Term {
    Constant(String),
    QUVar(u32),    //Query Variable
    EQVar(String), //Existentialy Quantified Variable
    AQVar(String),
}

impl Term {
    pub fn to_string(&self) -> String {
        match self {
            Term::Constant(symbol) => symbol.to_string(),
            Term::EQVar(symbol) => symbol.to_string(),
            Term::QUVar(id) => "_".to_string() + &id.to_string(),
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
            Term::QUVar(_) => 2,
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
            Term::QUVar(_) => 2,
            Term::EQVar(_) => 1,
            Term::AQVar(_) => 0,
        };
        match order1 < order2 {
            true => Some((self, other)),
            false => Some((other, self)),
        }
    }

    pub fn enum_type(&self) -> &str{
        match self {
            Term::Constant(_) => "Constant",
            Term::QUVar(_) => "QUVar",
            Term::EQVar(_) => "EQVar",
            Term::AQVar(_) => "AQVar",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Substitution {
    pub subs: HashMap<Term, Term>,
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution {
            subs: HashMap::new(),
        }
    }

    pub fn to_string(&self) -> String {
        let mut buf = String::from("{");
        for (k, v) in self.subs.iter() {
            buf += &k.to_string();
            buf += "/";
            buf += &v.to_string();
            buf += ", ";
        }
        buf.pop();
        buf += "}";
        return buf;
    }

    pub fn get(&self, key: &Term) -> Option<&Term> {
        self.subs.get(key)
    }

    pub fn insert(&mut self, k: Term, v: Term) {
        self.subs.insert(k, v);
    }

    pub fn compound_sub(&self, k: &Term) -> Term {
        match self.subs.get(k) {
            Some(v) => self.compound_sub(v),
            None => k.clone(),
        }
    }

    pub fn simplify(&mut self) {
        let mut new_subs: HashMap<Term, Term> = HashMap::new();
        //For all values update with compound_sub
        for k in self.subs.keys() {
            new_subs.insert(k.clone(), self.compound_sub(k));
        }
        self.subs = new_subs;
    }

    pub fn universal_quantification(&self) -> Substitution {
        let mut ho_sub = Substitution::new();
        for (t1, t2) in &self.subs {
            match t1 {
                Term::AQVar(symbol) => ho_sub.insert(t1.clone(), Term::EQVar(symbol.to_string())),
                _ => ho_sub.insert(t1.clone(), t2.clone()),
            }
        }
        return ho_sub;
    }

    pub fn unmapped_to_qu(&mut self, terms: Vec<&Term>, id_counter: &mut u32) {
        for term in terms {
            self.subs.insert(term.clone(), Term::QUVar(*id_counter));
            *id_counter += 1;
        }
    }

    pub fn unify(&mut self, other: Substitution) -> Option<Substitution>{
        let mut new_sub = self.clone();
        for (k,v1) in other.subs {
            match self.subs.get(&k) {
                Some(v2) => {match v1.unify(v2){
                    Some((t1,t2)) => new_sub.insert(k, t2.clone()),
                    None => return None,
                };},
                None => {new_sub.insert(k, v1);},
            };
        }
        return Some(new_sub);
    }

    pub fn filter(&mut self){
        let mut key_to_remove = vec![];
        for key in self.subs.keys(){
            match key {
                Term::QUVar(_) => (),
                _ => {key_to_remove.push(key.clone());}
            }
        }
        for key in key_to_remove{
            self.subs.remove(&key);
        }
    }
}

impl ops::Add<Substitution> for Substitution {
    type Output = Substitution;

    fn add(self, rhs: Substitution) -> Substitution {
        let mut res = Substitution::new();
        for (k, v) in self.subs.iter() {
            res.insert(k.clone(), v.clone())
        }
        for (k, v) in rhs.subs.iter() {
            res.insert(k.clone(), v.clone())
        }
        res.simplify();
        return res;
    }
}

impl AddAssign<Substitution> for Substitution {
    fn add_assign(&mut self, rhs: Substitution) {
        for (k,v) in rhs.subs{
            self.subs.insert(k, v);
        }
    }
}
