use std::ops::Sub;

use crate::terms::{Term, SubstitutionHandler, Substitution};

const MAX_HEAP_SIZE: usize = 1000;

pub type Binding = (usize,usize);
pub type Heap = Vec<Term>;
pub trait HeapHandler {
    fn new() -> Self;
    fn get_term(&self, i: usize) -> &Term ;
    fn deref(&self, i: usize) -> usize;
    fn new_term(&mut self, term: Option<Term>) -> usize;
    fn unify(&self, i1: usize, i2: usize) -> Option<(usize, usize)>;
    fn print_heap(&self);
    fn bind(&mut self, binding: &Substitution);
    fn unbind(&mut self, binding: &Substitution);
}

impl HeapHandler for Heap {
    fn new() -> Heap {
        Vec::with_capacity(MAX_HEAP_SIZE)
    }

    fn get_term(&self, i: usize) -> &Term {
        &self[self.deref(i)]
    }
    
    fn deref(&self, addr1: usize) -> usize{
        if let Term::REF(addr2) = self[addr1]{
            if addr1 == addr2 {
                addr1
            }else{
                self.deref(addr2)
            }
        }else {
            addr1
        }
    }
    
    fn new_term(&mut self, term: Option<Term>) -> usize {
        match term {
            Some(t) => {
                if let Some(i) = self.iter().position(|t2| t == *t2) {
                    return i;
                }
                self.push(t);
                self.len() - 1
            }
            None => {
                let i = self.len();
                self.push(Term::REF(i));
                i
            }
        }
    }
    
    fn unify(&self, i1: usize, i2: usize) -> Option<(usize, usize)> {
        let t1 = self.get_term(i1);
        let t2 = self.get_term(i2);
        if let Some((s1, _s2)) = t1.unify(t2) {
            if s1 == t1 {
                Some((i1, i2))
            } else {
                Some((i2, i1))
            }
        } else {
            None
        }
    }
    
    // fn apply_sub(&mut self, subs: &Substitution) {
    //     for (i1, i2) in &subs.subs {
    //         if let Term::REF(_) = self[*i1] {
    //             self[*i1] = Term::REF(*i2);
    //         }
    //     }
    // }
    
    // fn undo_sub(&mut self, subs: &Substitution) {
    //     for i in subs.subs.keys() {
    //         if let Term::REF(_) = self.heap[*i] {
    //             self.heap[*i] = Term::REF(*i);
    //         }
    //     }
    // }

    fn print_heap(&self){
        println!("|---|---------------|");
        for i in 0..self.len(){
            println!("|{:03}|{:width$}|",i,self[i].to_string(), width = 15);
            println!("|---|---------------|");
        }
    }

    fn bind(&mut self, binding: &Substitution){
        for (k,v) in binding{
            let a1 = self.deref(*k);
            let a2 = self.deref(*v);
            // println!("a1:{a1},a2:{a2}");
            self[a1] = Term::REF(a2);
        }
    }

    fn unbind(&mut self, binding: &Substitution) {
        for (k,_) in binding{
            self[*k] = Term::REF(*k)
        }
    }
}

