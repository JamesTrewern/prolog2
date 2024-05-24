use core::hash;
use std::{collections::HashMap, env::var};
use crate::{heap::{self, Cell, Heap, Tag}, parser::parse_literals, term::Term, unification::*};

static IMPLICATION: &'static str = ":-";

pub type Clause = [usize];

pub trait ClauseTraits {
    fn vars(&self, heap: &Heap) -> Vec<usize>;
    fn symbol_arity(&self, heap: &Heap) -> (usize, usize);
    fn parse_clause(terms: &[&str], heap: &mut Heap) -> Result<(ClauseType, Box<Clause>),String>;
    fn deallocate(&self, heap: &mut Heap);
    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool;
    fn to_string(&self, heap: &Heap) -> String;
    fn new(head: usize, body: &[usize]) -> Box<Self>;
}

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum ClauseType {
    CLAUSE,
    BODY,
    META,
    HYPOTHESIS,
}

impl ClauseTraits for Clause {
    fn new(head: usize, body: &[usize]) -> Box<Clause> {
        [&[head], body].concat().into()
    }

    fn to_string(&self, heap: &Heap) -> String {
        if self.len() == 1 {
            let clause_str = heap.term_string(self[0]);
            clause_str
        } else {
            let mut buffer: String = String::new();
            buffer += &heap.term_string(self[0]);
            buffer += ":-";
            let mut i = 1;
            loop {
                buffer += &heap.term_string(self[i]);
                i += 1;
                if i == self.len() {
                    break;
                } else {
                    buffer += ","
                }
            }
            buffer
        }
    }

    fn symbol_arity(&self, heap: &Heap) -> (usize, usize) {
        heap.str_symbol_arity(self[0])
    }

    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool {
        //TO DO
        //Implement proper Subsumtption
        if self.len() == other.len() {
            let mut binding = match unify(self[0], other[0], heap) {
                Some(b) => b,
                None => return false,
            };
            for i in 1..self.len() {
                if !unify_rec(self[i], other[i], heap, &mut binding) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    fn deallocate(&self, heap: &mut Heap) {
        for str_addr in self.iter().rev() {
            heap.deallocate_str(*str_addr);
        }
    }

    fn parse_clause(tokens: &[&str], heap: &mut Heap) -> Result<(ClauseType, Box<Clause>),String> {
        let terms = parse_literals(tokens)?;
        let clause_type = if terms.iter().any(|t| t.meta()){
            ClauseType::META
        }else{
            ClauseType::CLAUSE
        };
        let mut var_ref = HashMap::new();
        let literals: Box<Clause> = terms.iter().map(|t| t.build_on_heap(heap, &mut var_ref)).collect(); 
        Ok((clause_type, literals))
    }

    fn vars(&self, heap: &Heap) -> Vec<usize>{
        let mut vars = Vec::<usize>::new();
        for literal in self.iter(){
            vars.append(&mut heap.term_vars(*literal).iter().filter_map(|(tag,addr)| if *tag == Tag::REFC{ Some(*addr)}else{None}).collect());
        }
        vars.sort();
        vars.dedup();
        vars 
    }
}