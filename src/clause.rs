use std::{collections::HashMap, env::var};
use crate::{heap::Heap, unification::*};

static IMPLICATION: &'static str = ":-";

pub type Clause = [usize];

pub trait ClauseTraits {
    fn vars(&self, heap: &Heap) -> Vec<usize>;
    fn symbol_arity(&self, heap: &Heap) -> (usize, usize);
    fn parse_clause(clause: &str, heap: &mut Heap) -> (ClauseType, Box<Clause>);
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

    fn parse_clause(clause: &str, heap: &mut Heap) -> (ClauseType, Box<Clause>) {
        let (i3, uni_vars) = get_uni_vars(clause);

        let mut clause_type =
            if !uni_vars.is_empty() || clause.trim().chars().next().unwrap().is_uppercase() {
                ClauseType::META
            } else {
                ClauseType::CLAUSE
            };

        let (mut i1, i2) = match clause.find(IMPLICATION) {
            Some(i) => (i, i + IMPLICATION.len()),
            None => {
                //No implication present, build fact
                if clause.trim().chars().next().unwrap().is_uppercase() {
                    clause_type = ClauseType::META
                }
                let head = heap.build_literal(clause, &mut HashMap::new(), &uni_vars);
                return (clause_type, Clause::new(head, &[]));
            }
        };
        let head = &clause[..i1];
        let body = &clause[i2..i3];
        i1 = 0;
        let mut in_brackets = (0, 0);
        let mut body_literals: Vec<&str> = vec![];
        for (i2, c) in body.chars().enumerate() {
            match c {
                '(' => {
                    in_brackets.0 += 1;
                }
                ')' => {
                    if in_brackets.0 == 0 {
                        break;
                    }
                    in_brackets.0 -= 1;
                }
                '[' => {
                    in_brackets.1 += 1;
                }
                ']' => {
                    if in_brackets.1 == 0 {
                        break;
                    }
                    in_brackets.1 -= 1;
                }
                ',' => {
                    if in_brackets == (0, 0) {
                        body_literals.push(&body[i1..i2]);
                        if body[i1..i2].trim().chars().next().unwrap().is_uppercase()
                        {
                            clause_type = ClauseType::META;
                        }
                        i1 = i2 + 1
                    }
                }
                _ => (),
            }
            if i2 == body.len() - 1 {
                body_literals.push(body[i1..].trim());
            }
        }
        let mut map: HashMap<String, usize> = HashMap::new();
        let head = heap.build_literal(head, &mut map, &uni_vars);
        let body: Vec<usize> = body_literals
            .iter()
            .map(|text| heap.build_literal(text, &mut map, &uni_vars))
            .collect();

        (clause_type, Clause::new(head, &body))
    }

    fn vars(&self, heap: &Heap) -> Vec<usize>{
        let mut vars = Vec::<usize>::new();
        for literal in self.iter(){
            vars.append(&mut heap.get_term_object(*literal).vars())
        }
        vars.sort();
        vars.dedup();
        vars 
    }
}

fn get_uni_vars<'a>(clause: &'a str) -> (usize, Vec<&'a str>) {
    match clause.rfind('\\') {
        Some(i) => {
            if clause[i..].chars().any(|c| c == '"' || c == '\'') {
                (clause.len(), vec![])
            } else {
                (
                    i,
                    clause[i + 1..].split(',').map(|var| var.trim()).collect(),
                )
            }
        }
        None => (clause.len(), vec![]),
    }
}
