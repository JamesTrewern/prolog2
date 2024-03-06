use super::{substitution::Substitution, terms::Term};

const MAX_HEAP_SIZE: usize = 1000;
// pub type Heap = Vec<Term>;
// pub trait HeapHandler {
//     fn new() -> Self;
//     fn get_term(&self, i: usize) -> &Term ;
//     fn deref(&self, i: usize) -> usize;
//     fn new_term(&mut self, term: Option<Term>) -> usize;
//     fn unify(&self, i1: usize, i2: usize) -> Option<(usize, usize)>;
//     fn print_heap(&self);
//     fn bind(&mut self, binding: &Substitution);
//     fn unbind(&mut self, binding: &Substitution);
//     fn term_string(&self, addr: usize) -> String;
//     fn parse_term(&mut self, term: &str, aqvars: &Vec<&str>) -> usize;
// }

pub struct Heap{
    heap: Vec<Term>,
    strings: Vec<String>
}

impl Heap {
    pub fn new() -> Heap {
        Heap{    
            heap: Vec::with_capacity(MAX_HEAP_SIZE),
            strings: vec![],
        }
    }

    pub fn get_term(&self, i: usize) -> &Term {
        &self[self.deref(i)]
    }
    
    pub fn deref(&self, addr1: usize) -> usize{
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
    
    pub fn new_term(&mut self, term: Option<Term>) -> usize {
        match term {
            Some(t) => {
                if let Some(i) = self.heap.iter().position(|t2| t == *t2) {
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
    
    pub fn unify(&self, i1: usize, i2: usize) -> Option<(usize, usize)> {
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

    pub fn print_heap(&self){
        println!("|---|---------------|");
        for i in 0..self.heap.len(){
            println!("|{:03}|{:width$}|",i,self.term_string(i), width = 15);
            println!("|---|---------------|");
        }
    }

    pub fn bind(&mut self, binding: &Substitution){
        for (k,v) in binding{
            let a1 = self.deref(*k);
            let a2 = self.deref(*v);
            // println!("a1:{a1},a2:{a2}");
            self.heap[a1] = Term::REF(a2);
        }
    }

    pub fn unbind(&mut self, binding: &Substitution) {
        for (k,_) in binding{
            self.heap[*k] = Term::REF(*k)
        }
    }

    pub fn term_string(&self, addr: usize) -> String {
        match self.get_term(addr) {
            Term::Constant(symbol) => self.get_string(*symbol).to_string(),
            Term::EQVar(symbol) => self.get_string(*symbol).to_owned(),
            Term::REF(addr) => format!("_{addr}"),
            Term::AQVar(symbol) => format!("∀'{}",self.get_string(*symbol)),
            Term::Number(value) => value.to_string(),
            Term::List(_) => todo!(),
            Term::EmptyList => "[]".to_string(),
        }
    }

    fn add_string(&mut self, string: &str) -> usize{
         match self.strings.iter().position(|string2| string == string2){
            Some(i) => i,
            None => {self.strings.push(string.to_string());self.strings.len()-1},
        }
        
    }

    pub fn get_string(&self, i: usize) -> &str{
        &self.strings[i]
    }

    pub fn parse_term(&mut self, mut term_str: &str, aqvars: &Vec<&str>) -> usize {
        term_str = term_str.trim();
        if term_str.starts_with('[') && term_str.ends_with(']'){
            //TO DO easy empty list 
            let mut tail: usize = self.new_term(Some(Term::EmptyList));
            for term in term_str[1..term_str.len()].split(',').rev(){
                let h = self.parse_term(term, aqvars);
                tail = self.new_term(Some(Term::List((h,tail))));
            }
            tail
        }else{
            if let Ok(value) = term_str.parse::<f64>(){
                return self.new_term(Some(Term::Number(value)));
            }
            let str_i = self.add_string(term_str);
            if term_str.chars().next().unwrap().is_uppercase(){
                if aqvars.contains(&term_str){
                    self.new_term(Some(Term::AQVar(str_i)))
                }else{
                    self.new_term(Some(Term::EQVar(str_i)))
                }
            }else{
                self.new_term(Some(Term::Constant(str_i)))
            }
        }
    }
}

use std::ops::Index;

impl Index<usize> for Heap {
    type Output = Term;

    fn index(&self, index: usize) -> &Term {
        &self.heap[index]
    }

    
}