use super::heap::{Heap, HeapHandler};

pub type Substitution = Vec<(usize, usize)>;

pub trait SubstitutionHandler {
    // fn filter(&mut self, heap: &Heap);
    fn unify(&mut self, other: Substitution, heap: &Heap) -> Option<Substitution>;
    // fn universal_quantification(&self, heap: &mut Heap) -> Substitution;
    fn get_sub(&self, i1: usize) -> Option<usize>;
    fn insert_sub(&mut self, k: usize, value: usize);
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
        self.iter().find(|(i2, _)| i1 == *i2).is_some()
    }

    fn bindings(&self, heap: &Heap) -> Vec<(usize, usize)> {
        let mut bindings = Substitution::new();
        for (t1, t2) in self {
            if heap[*t1].enum_type() == "Ref" {
                bindings.push((*t1, *t2));
            }
        }
        return bindings;
    }

    fn get_sub(&self, i1: usize) -> Option<usize> {
        for (i2, v) in self {
            if i1 == *i2 {
                return Some(*v);
            }
        }
        return None;
    }

    fn insert_sub(&mut self, k: usize, v: usize) {
        self.push((k, v));
    }

    fn meta(&self, heap: &Heap) -> Substitution {
        let mut new_sub = self.clone();
        new_sub.retain(|(k, _v)| heap.get_term(*k).enum_type() != "AQVar");
        return new_sub;
    }

    fn unify(&mut self, other: Substitution, heap: &Heap) -> Option<Substitution> {
        let mut new_sub = self.clone();
        for (k, v1) in other {
            match self.get_sub(k) {
                Some(v2) => {
                    match heap.unify(v1, v2) {
                        Some((_t1, t2)) => new_sub.insert_sub(k, t2),
                        None => return None,
                    };
                }
                None => {
                    new_sub.insert_sub(k, v1);
                }
            };
        }
        return Some(new_sub);
    }
}
