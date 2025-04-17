use std::{collections::HashMap, mem};

use super::syntax_tree::{Clause, Term, Unit};
use crate::heap::{
    heap::{Cell, Heap, Tag, EMPTY_LIS},
    symbol_db::SymbolDB,
};

pub(crate) fn execute_tree(syntax_tree: Vec<Clause>) {
    for clause in syntax_tree {
        match clause {
            Clause::Fact(term) => todo!(),
            Clause::Rule(term, terms) => todo!(),
            Clause::MetaRule(term, terms) => todo!(),
            Clause::Directive(terms) => todo!(),
        }
    }
}

impl Unit {
    pub fn encode(
        &self,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        match self {
            Unit::Constant(symbol) => {
                let id = SymbolDB::set_const(symbol.clone());
                heap.heap_push((Tag::Con, id))
            }
            Unit::Variable(symbol) => match var_values.get(symbol) {
                Some(ref_addr) if query => heap.heap_push((Tag::Ref, *ref_addr)),
                Some(arg) => heap.heap_push((Tag::Arg, *arg)),
                None if query => heap.set_ref(None),
                None => heap.heap_push((Tag::Arg, var_values.len())),
            },
            Unit::Int(value) => heap.heap_push((Tag::Int, unsafe { mem::transmute_copy(value) })),
            Unit::Float(value) => heap.heap_push((Tag::Flt, unsafe { mem::transmute_copy(value) })),
            Unit::String(text) => {
                let str_id = SymbolDB::set_string(text.clone());
                heap.heap_push((Tag::Stri, str_id))
            }
        }
    }
}

impl Term {
    fn unit(&self) -> bool {
        matches!(self, Term::Unit(_) | Term::EmptyList)
    }

    fn encode(
        &self,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        match self {
            Term::Unit(unit) => unit.encode(heap, var_values, query),
            Term::Atom(unit, terms) => Self::encode_func(unit, terms, heap, var_values, query),
            Term::List(head, tail) => Self::encode_list(head, tail, heap, var_values, query),
            Term::Tuple(terms) => Self::encode_tup(terms, heap, var_values, query),
            Term::Set(terms) => Self::encode_set(terms, heap, var_values, query),
            Term::EmptyList => heap.heap_push(EMPTY_LIS),
        }
    }

    fn pre_encode_complex(
        &self,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> Option<Cell>{
        if self.unit() {
            None
        } else {
            let tag = if matches!(self, Term::List(_, _)) {
                Tag::Lis
            } else {
                Tag::Str
            };
            Some((tag, self.encode(heap, var_values, query)))
        }
    }

    fn pre_encode_complex_terms(
        terms: &Vec<Term>,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> Vec<Option<Cell>> {
        let complex_terms = terms.iter().map(|term| term.pre_encode_complex(heap, var_values, query)).collect();

        complex_terms
    }

    fn encode_tup(
        terms: &Vec<Term>,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = terms.iter().map(|term| term.pre_encode_complex(heap, var_values, query)).collect();

        let addr = heap.heap_push((Tag::Tup, terms.len()));

        for (complex, term) in complex_terms.iter().zip(terms.iter()) {
            match complex {
                Some(cell) => heap.heap_push(*cell),
                None => term.encode(heap, var_values, query),
            };
        }

        addr
    }

    fn encode_set(
        terms: &Vec<Term>,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let mut terms_set: Vec<Term> = vec![];
        for term in terms {
            if !terms_set.contains(term) {
                terms_set.push(term.clone());
            }
        }

        let complex_terms: Vec<Option<Cell>> = terms_set.iter().map(|term| term.pre_encode_complex(heap, var_values, query)).collect();


        let addr = heap.heap_push((Tag::Set, terms_set.len()));

        for (complex, term) in complex_terms.iter().zip(terms_set.iter()) {
            match complex {
                Some(cell) => heap.heap_push(*cell),
                None => term.encode(heap, var_values, query),
            };
        }

        addr
    }

    fn encode_func(
        unit: &Unit,
        terms: &Vec<Term>,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = terms.iter().map(|term| term.pre_encode_complex(heap, var_values, query)).collect();
        let addr = heap.heap_push((Tag::Func, terms.len() + 1));
        unit.encode(heap, var_values, query);
        for (complex, term) in complex_terms.iter().zip(terms.iter()) {
            match complex {
                Some(cell) => heap.heap_push(*cell),
                None => term.encode(heap, var_values, query),
            };
        }

        addr
    }

    fn encode_list(
        head: &Vec<Term>,
        tail: &Box<Term>,
        heap: &mut Vec<Cell>,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = head.iter().map(|term| term.pre_encode_complex(heap, var_values, query)).collect();
        let complex_tail = tail.pre_encode_complex(heap, var_values, query);
        
        let addr = heap.heap_len();

        for (complex, term) in complex_terms.iter().zip(head.iter()).rev().skip(1).rev() {
            match complex {
                Some(cell) => heap.heap_push(*cell),
                None => term.encode(heap, var_values, query),
            };
            heap.push((Tag::Lis,heap.len()));
        }

        let (complex, term) = (complex_terms.last().unwrap(),head.last().unwrap());
        match complex {
            Some(cell) => heap.heap_push(*cell),
            None => term.encode(heap, var_values, query),
        };

        match complex_tail {
            Some(cell) => heap.heap_push(cell),
            None => tail.encode(heap, var_values, query),
        };

        addr
    }
}
