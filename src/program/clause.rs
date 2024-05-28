use crate::{
    heap::heap::{Heap, Tag},
    interface::term::Term,
};
use std::{collections::HashMap, mem::ManuallyDrop, ops::Deref};

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub(crate) enum ClauseType {
    CLAUSE,
    BODY,
    META,
    HYPOTHESIS,
}

pub(crate) struct Clause {
    pub clause_type: ClauseType,
    pub literals: ManuallyDrop<Box<[usize]>>,
}

impl Clause {
    pub fn new(head: usize, body: &[usize], clause_type: ClauseType) -> Clause {
        Clause {
            clause_type,
            literals:  ManuallyDrop::new([&[head], body].concat().into()),
        }
    }

    pub fn to_string(&self, heap: &Heap) -> String {
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

    pub fn symbol_arity(&self, heap: &Heap) -> (usize, usize) {
        heap.str_symbol_arity(self[0])
    }

    pub fn parse_clause(terms: Vec<Term>, heap: &mut Heap) -> Clause {
        let clause_type = if terms.iter().any(|t| t.meta()) {
            ClauseType::META
        } else {
            ClauseType::CLAUSE
        };
        let mut var_ref = HashMap::new();
        let literals: ManuallyDrop<Box<[usize]>> = ManuallyDrop::new(terms
            .iter()
            .map(|t| t.build_on_heap(heap, &mut var_ref))
            .collect::<Box<[usize]>>());
        Clause { clause_type, literals}
    }

    pub fn symbolise_vars(&self, heap: &mut Heap) {
        let mut vars = Vec::<usize>::new();
        for literal in self.iter() {
            vars.append(
                &mut heap
                    .term_vars(*literal)
                    .iter()
                    .filter_map(|(tag, addr)| if *tag == Tag::REF { Some(*addr) } else { None })
                    .collect(),
            );
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

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}