use std::{ops::Index, cell::Ref};

use crate::terms::{Term, Substitution};

const MAX_HEAP_SIZE: usize = 1000;
#[derive(Debug)]
pub struct Heap {
    pub heap: Vec<Term>,
}

impl Heap {
    pub fn new() -> Heap{
        Heap{heap: Vec::with_capacity(MAX_HEAP_SIZE)}
    }

    pub fn get_term(&self, i: usize) -> &Term {
        let mut prev_i = i;
        loop {
            match &self.heap[prev_i] {
                Term::REF(new_i) => {
                    if prev_i == *new_i {
                        return &self.heap[prev_i];
                    } else {
                        prev_i = *new_i;
                    }
                }
                v => return v,
            }
        }
    }
    pub fn get_i(&self, term: &Term) -> usize{
        self.heap.iter().position(|term2| *term == *term2).unwrap()
    }
    pub fn new_term(&mut self, term: Option<Term>) -> usize {
        match term {
            Some(t) => {
                if let Some(i) =  self.heap.iter().position(|t2| t==*t2) {
                    return i;
                }
                self.heap.push(t);
                self.heap.len() - 1
            }
            None => {
                let i = self.heap.len();
                self.heap.push(Term::REF(i));
                i
            }
        }
    }
    pub fn unify(&self, i1: usize, i2:usize) ->Option<(usize, usize)>{
        let t1 = self.get_term(i1);
        let t2 = self.get_term(i2);
        if let Some((s1,s2)) = t1.unify(t2){
            if s1 == t1{
                Some((i1,i2))
            }else {
                Some((i2,i1))
            }
        }else{
            None
        }
    }
    pub fn apply_sub(&mut self, subs: &Substitution) {
        for (i1, i2) in &subs.subs {
            if let Term::REF(_) = self.heap[*i1] {
                self.heap[*i1] = Term::REF(*i2);
            }
        }
    }
    pub fn undo_sub(&mut self, subs: &Substitution) {
        for i in subs.subs.keys() {
            if let Term::REF(_) = self.heap[*i] {
                self.heap[*i] = Term::REF(*i);
            }
        }
    }
}

impl Index<usize> for Heap{
    type Output = Term;

    fn index(&self, i: usize) -> &Term {
        &self.heap[i]
    }
}
