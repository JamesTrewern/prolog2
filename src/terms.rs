use crate::heap::{Heap, HeapHandler};

//TO DO 
// aq to eq function
// Term string value to be pointers to heap attribute of all strings

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Term {
    Number(f64),
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
            Term::Number(value) => value.to_string(),
        }
    }
    pub fn unify<'a>(&'a self, other: &'a Term) -> Option<(&'a Term, &'a Term)> {
        if self == other{ return Some((self, other));}
        if let &Term::Constant(value1) = &self {
            if let &Term::Constant(value2) = &other {
                if value1 != value2 {
                    return None;
                }
            }
        }
        let order1 = self.order();
        let order2 = other.order();
        if order1 == 0 && order2 == 0{
            return None;
        }
        match order1 > order2 {
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
            Term::Number(_) => "Num",
        }
    }

    pub fn order(&self) -> usize{
        match self {
            Term::Number(_) => 0,
            Term::Constant(_) => 0,
            Term::REF(_) => 1,
            Term::EQVar(_) => 2,
            Term::AQVar(_) => 3,
            
        }
    }
}

pub type Substitution = Vec<(usize,usize)>;

pub trait SubstitutionHandler {
    // fn filter(&mut self, heap: &Heap);
    fn unify(&mut self, other: Substitution, heap: &Heap) -> Option<Substitution>;
    // fn universal_quantification(&self, heap: &mut Heap) -> Substitution;
    fn get_sub(&self,i1: usize) -> Option<usize>;
    fn insert_sub(&mut self, k:usize, value: usize);
    fn bindings(&self, heap: &Heap) -> Substitution;
    fn to_string(&self, heap: &Heap) -> String;
    fn contains_key(&self, i1: usize) -> bool;
    fn meta(&self, heap: &Heap) -> Substitution;
}

impl SubstitutionHandler for Substitution {
    fn to_string(&self, heap: &Heap) -> String {
        let mut buf = String::from("{");
        for (k, v) in self.iter() {
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

    // fn universal_quantification(&self, heap: &mut Heap) -> Substitution {
    //     let mut ho_sub = Substitution::new();
    //     for (i1, i2) in self {
    //         let t1 = heap.get_term(*i1);
    //         match t1 {
    //             Term::AQVar(symbol) => {
    //                 let i3 = heap.new_term(Some(Term::EQVar(symbol.clone())));
    //                 ho_sub.insert(*i1, i3);
    //             },
    //             _ => {
    //                 ho_sub.insert(*i1, *i2);
    //             },
    //         };
    //     }
    //     return ho_sub;
    // }

    fn contains_key(&self, i1: usize) -> bool {
        self.iter().find(|(i2,_)| i1 == *i2).is_some()
    }

    fn bindings(&self, heap: &Heap)-> Vec<(usize, usize)> {
        let mut bindings = Substitution::new();
        for (t1, t2) in self{
            if heap[*t1].enum_type() == "Ref"{
                bindings.push((*t1,*t2));
            }
        }
        return bindings;
    }

    fn get_sub(&self,i1: usize) -> Option<usize> {
        for (i2,v) in self {
            if i1 == *i2 {
                return Some(*v);
            }
        }
        return None;
    }

    fn insert_sub(&mut self, k:usize, v: usize) {
        self.push((k,v));
    }

    fn meta(&self, heap: &Heap) -> Substitution {
        let mut new_sub = self.clone();
        new_sub.retain(|(k,v)|heap.get_term(*k).enum_type()!="AQVar");
        return new_sub;
    }

    fn unify(&mut self, other: Substitution, heap: &Heap) -> Option<Substitution>{
        let mut new_sub = self.clone();
        for (k,v1) in other {
            match self.get_sub(k) {
                Some(v2) => {match heap.unify(v1, v2){
                    Some((t1,t2)) => new_sub.insert_sub(k, t2),
                    None => return None,
                };},
                None => {new_sub.insert_sub(k, v1);},
            };
        }
        return Some(new_sub);
    }
}
