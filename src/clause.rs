use std::collections::HashMap;
use crate::{heap::{Cell, Heap, Tag}, parser::parse_literals};

pub type Clause = [usize];

pub trait ClauseTraits {
    fn symbolise_vars(&self, heap: &mut Heap);
    fn symbol_arity(&self, heap: &Heap) -> (usize, usize);
    fn parse_clause(terms: &[&str], heap: &mut Heap) -> Result<(ClauseType, Box<Clause>),String>;
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

    fn symbolise_vars(&self, heap: &mut Heap){
        let mut vars = Vec::<usize>::new();
        for literal in self.iter(){
            vars.append(&mut heap.term_vars(*literal).iter().filter_map(|(tag,addr)| if *tag == Tag::REF { Some(*addr)}else{None}).collect());
        }
        vars.sort();
        vars.dedup();

        let mut alphabet = (b'A'..=b'Z').map(|c| String::from_utf8(vec![c]).unwrap());
        for var in vars {
            let symbol = alphabet.next().unwrap();
            heap.symbols.set_var(&symbol, var)
        }
    }
}