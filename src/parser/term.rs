use std::{collections::HashMap, mem};

use fsize::fsize;

use crate::heap::{heap::{Cell, Heap, Tag, EMPTY_LIS}, symbol_db::SymbolDB};

#[derive(Debug, PartialEq, Clone)]
pub enum Unit {
    Constant(String),
    Variable(String),
    Int(isize),
    Float(fsize),
    String(String),
}

impl Unit {
    fn is_atom(token: &str) -> bool {
        token.chars().next().map_or(false, |c| {
            c.is_lowercase() || c == '\'' && token.chars().last().map_or(false, |c| c == '\'')
        })
    }

    fn is_string(token: &str) -> bool {
        token.chars().next().map_or(false, |c| {
            c == '"' && token.chars().last().map_or(false, |c| c == '"')
        })
    }

    //Is variable if begins with _ or uppercase
    fn is_variable(token: &str) -> bool {
        token
            .chars()
            .next()
            .map_or(false, |c| c.is_uppercase() || c == '_')
            && token.chars().all(|c| c.is_alphanumeric() || c == '_')
    }

    // fn is_numeric(token: &str) -> bool {
    //     token.chars().all(|c| c.is_ascii_digit() || c == '.')
    // }

    // fn is_atom_var(token: &str) -> bool {
    //     Unit::is_atom(token) || Unit::is_variable(token)
    // }

    // fn is_unit(token: &str) -> bool {
    //     Unit::is_numeric(token) || Unit::is_atom_var(token) || Unit::is_string(token)
    // }

    pub fn parse_unit(token: &str) -> Option<Self> {
        if Unit::is_variable(token) {
            Some(Unit::Variable(token.into()))
        } else if Unit::is_atom(token) {
            if token.chars().next().unwrap() == '\'' {
                Some(Unit::Constant(token[1..token.len() - 1].into()))
            } else {
                Some(Unit::Constant(token.into()))
            }
        } else if Unit::is_string(token) {
            Some(Unit::String(token.to_string()))
        } else if let Ok(num) = token.parse::<isize>() {
            Some(Unit::Int(num))
        } else if let Ok(num) = token.parse::<fsize>() {
            Some(Unit::Float(num))
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Unit(Unit),
    Atom(Unit, Vec<Term>),
    List(Vec<Term>, Box<Term>),
    Tuple(Vec<Term>),
    Set(Vec<Term>),
    EmptyList,
}


impl Unit {
    fn encode_var(
        symbol: &String,
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        match var_values.get(symbol) {
            Some(ref_addr) if query => heap.heap_push((Tag::Ref, *ref_addr)),
            Some(arg) => {
                let addr = heap.heap_push((Tag::Arg, *arg));
                SymbolDB::set_var(symbol.clone(), addr, heap.get_id());
                addr
            }
            None if query => {
                let addr = heap.set_ref(None);
                var_values.insert(symbol.clone(), addr);
                SymbolDB::set_var(symbol.clone(), addr, heap.get_id());
                addr
            }
            None => {
                let v = var_values.len();
                var_values.insert(symbol.clone(), v);
                let addr = heap.heap_push((Tag::Arg, v));
                SymbolDB::set_var(symbol.clone(), addr, heap.get_id());
                addr
            }
        }
    }

    pub fn encode(
        &self,
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        match self {
            Unit::Constant(symbol) => {
                let id = SymbolDB::set_const(symbol.clone());
                heap.heap_push((Tag::Con, id))
            }
            Unit::Variable(symbol) => Self::encode_var(symbol, heap, var_values, query),
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

    pub fn encode(
        &self,
        heap: &mut impl Heap,
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
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> Option<Cell> {
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

    // fn pre_encode_complex_terms(
    //     terms: &Vec<Term>,
    //     heap: &mut impl Heap,
    //     var_values: &mut HashMap<String, usize>,
    //     query: bool,
    // ) -> Vec<Option<Cell>> {
    //     let complex_terms = terms
    //         .iter()
    //         .map(|term| term.pre_encode_complex(heap, var_values, query))
    //         .collect();

    //     complex_terms
    // }

    fn encode_tup(
        terms: &Vec<Term>,
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = terms
            .iter()
            .map(|term| term.pre_encode_complex(heap, var_values, query))
            .collect();

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
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let mut terms_set: Vec<Term> = vec![];
        for term in terms {
            if !terms_set.contains(term) {
                terms_set.push(term.clone());
            }
        }

        let complex_terms: Vec<Option<Cell>> = terms_set
            .iter()
            .map(|term| term.pre_encode_complex(heap, var_values, query))
            .collect();

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
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = terms
            .iter()
            .map(|term| term.pre_encode_complex(heap, var_values, query))
            .collect();
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
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let complex_terms: Vec<Option<Cell>> = head
            .iter()
            .map(|term| term.pre_encode_complex(heap, var_values, query))
            .collect();
        let complex_tail = tail.pre_encode_complex(heap, var_values, query);

        let addr = heap.heap_len();

        for (complex, term) in complex_terms.iter().zip(head.iter()).rev().skip(1).rev() {
            match complex {
                Some(cell) => heap.heap_push(*cell),
                None => term.encode(heap, var_values, query),
            };
            heap.heap_push((Tag::Lis, heap.heap_len()+1));
        }

        let (complex, term) = (complex_terms.last().unwrap(), head.last().unwrap());
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

#[cfg(test)]
mod encode_tests {
    use std::{collections::HashMap, sync::Arc};

    use super::{Term, Unit};
    use crate::heap::{
        query_heap::QueryHeap,
        heap::{Heap, Tag, EMPTY_LIS},
        symbol_db::SymbolDB,
    };

    use fsize::fsize;

    #[test]
    fn encode_argument() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);
        let mut var_values = HashMap::new();
        let x = Unit::Variable("X".into());
        let y = Unit::Variable("Y".into());
        x.encode(&mut heap.cells, &mut var_values, false);
        y.encode(&mut heap.cells, &mut var_values, false);
        x.encode(&mut heap.cells, &mut var_values, false);
        y.encode(&mut heap.cells, &mut var_values, false);

        assert_eq!(
            heap.cells,
            [(Tag::Arg, 0), (Tag::Arg, 1), (Tag::Arg, 0), (Tag::Arg, 1),]
        );

        heap.cells = vec![];
        drop(heap.cells);

    }

    #[test]
    fn encode_ref() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);
        heap.cells = vec![];
        let mut var_values = HashMap::new();
        let x = Unit::Variable("X".into());
        let y = Unit::Variable("Y".into());
        x.encode(&mut heap.cells, &mut var_values, true);
        y.encode(&mut heap.cells, &mut var_values, true);
        x.encode(&mut heap.cells, &mut var_values, true);
        y.encode(&mut heap.cells, &mut var_values, true);

        assert_eq!(
            heap.cells,
            [(Tag::Ref, 0), (Tag::Ref, 1), (Tag::Ref, 0), (Tag::Ref, 1),]
        );

        heap.cells = vec![];
        drop(heap.cells);

    }

    #[test]
    fn encode_unit() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);
        heap.cells = vec![];
        let a = SymbolDB::set_const("a".into());

        let unit = Unit::Constant("a".into());
        let addr = unit.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "a");
        assert_eq!(heap.cells, [(Tag::Con, a)]);

        heap.cells = vec![];
        let unit = Unit::Int(10);
        let addr = unit.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "10");
        assert_eq!(heap.cells, [(Tag::Int, 10)]);

        heap.cells = vec![];
        let value: isize = -10;
        let unit = Unit::Int(value);
        let addr = unit.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "-10");
        assert_eq!(heap.cells, [(Tag::Int, isize::cast_unsigned(value) )]);

        heap.cells = vec![];
        let value: fsize = 1.1;
        let unit = Unit::Float(value);
        let addr = unit.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "1.1");

        #[cfg(target_pointer_width = "32")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        #[cfg(target_pointer_width = "64")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        heap.cells = vec![];
        let value: fsize = -1.1;
        let unit = Unit::Float(value);
        let addr = unit.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "-1.1");

        #[cfg(target_pointer_width = "32")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        #[cfg(target_pointer_width = "64")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        heap.cells = vec![];
        drop(heap.cells);

    }

    #[test]
    fn program_encode_functor() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![Term::Unit(x.clone()), Term::Unit(a.clone())],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        SymbolDB::_see_var_map();
        assert_eq!(heap.cells.term_string(addr), "p(X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            q.clone(),
            vec![Term::Unit(a.clone()), Term::Unit(q.clone())],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "Q(a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 3),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "p(f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "p((f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "p({f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::List(
                    vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                    Box::new(Term::EmptyList),
                ),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "p([f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Arg, 0),
            ]
        );
        drop(heap.cells);

    }

    #[test]
    fn query_encode_functor() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![Term::Unit(x.clone()), Term::Unit(a.clone())],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "p(X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 2),
                (Tag::Con, a_id),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            q.clone(),
            vec![Term::Unit(a.clone()), Term::Unit(q.clone())],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "Q(a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 3),
                (Tag::Ref, 1),
                (Tag::Con, a_id),
                (Tag::Ref, 1),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "p(f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "p((f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "p({f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Atom(
            p.clone(),
            vec![
                Term::List(
                    vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                    Box::new(Term::EmptyList),
                ),
                Term::Unit(x.clone()),
            ],
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "p([f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Ref, 2),
                EMPTY_LIS,
                (Tag::Func, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Ref, 2),
            ]
        );
        drop(heap.cells);
    }

    #[test]
    fn program_encode_tuple() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Unit(x.clone()),
            Term::Unit(a.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(p,X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(q.clone()),
            Term::Unit(a.clone()),
            Term::Unit(q.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(Q,a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(p,f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(p,(f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(p,{f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::List(
                vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                Box::new(Term::EmptyList),
            ),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "(p,[f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Arg, 0),
            ]
        );
        drop(heap.cells);

    }

    #[test]
    fn query_encode_tuple() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Unit(x.clone()),
            Term::Unit(a.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(p,X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 2),
                (Tag::Con, a_id),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(q.clone()),
            Term::Unit(a.clone()),
            Term::Unit(q.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(Q,a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Ref, 1),
                (Tag::Con, a_id),
                (Tag::Ref, 1),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(p,f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(p,(f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(p,{f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Tuple(vec![
            Term::Unit(p.clone()),
            Term::List(
                vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                Box::new(Term::EmptyList),
            ),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "(p,[f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Ref, 2),
                EMPTY_LIS,
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Ref, 2),
            ]
        );
        drop(heap.cells);
    }

    #[test]
    fn program_encode_set() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(a.clone()),
            Term::Unit(x.clone()),
            Term::Unit(a.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{a,X}");
        assert_eq!(heap.cells, [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Arg, 0),]);

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(q.clone()),
            Term::Unit(a.clone()),
            Term::Unit(q.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{Q,a}");
        assert_eq!(heap.cells, [(Tag::Set, 2), (Tag::Arg, 0), (Tag::Con, a_id),]);

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{p,f(X),X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{p,(f,X),X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{p,{f,X},X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Arg, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::List(
                vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                Box::new(Term::EmptyList),
            ),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        assert_eq!(heap.cells.term_string(addr), "{p,[f,X],X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Arg, 0),
            ]
        );
    }

    #[test]
    fn query_encode_set() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let f_id = SymbolDB::set_const("f".into());

        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(a.clone()),
            Term::Unit(x.clone()),
            Term::Unit(a.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{a,X}");
        assert_eq!(heap.cells, [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Ref, 2),]);

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(q.clone()),
            Term::Unit(a.clone()),
            Term::Unit(q.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{Q,a}");
        assert_eq!(heap.cells, [(Tag::Set, 2), (Tag::Ref, 1), (Tag::Con, a_id),]);

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Atom(f.clone(), vec![Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{p,f(X),X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Func, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Tuple(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{p,(f,X),X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::Set(vec![Term::Unit(f.clone()), Term::Unit(x.clone())]),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{p,{f,X},X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 2),
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Str, 0),
                (Tag::Ref, 2),
            ]
        );

        heap.cells = vec![];
        let term = Term::Set(vec![
            Term::Unit(p.clone()),
            Term::List(
                vec![Term::Unit(f.clone()), Term::Unit(x.clone())],
                Box::new(Term::EmptyList),
            ),
            Term::Unit(x.clone()),
        ]);
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        assert_eq!(heap.cells.term_string(addr), "{p,[f,X],X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, f_id),
                (Tag::Lis, 2),
                (Tag::Ref, 2),
                EMPTY_LIS,
                (Tag::Set, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Ref, 2),
            ]
        );
        drop(heap.cells);
    }

    #[test]
    fn program_encode_list() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let a_id = SymbolDB::set_const("a".into());

        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let a = Unit::Constant("a".into());

        heap.cells = vec![];
        let term = Term::List(
            vec![
                Term::Unit(a.clone()),
                Term::Unit(x.clone()),
                Term::Unit(a.clone()),
            ],
            Box::new(Term::EmptyList),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[a,X,a]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, a_id),
                (Tag::Lis, 2),
                (Tag::Arg, 0),
                (Tag::Lis, 4),
                (Tag::Con, a_id),
                EMPTY_LIS,
                (Tag::Lis, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::List(
            vec![Term::Unit(q.clone()), Term::Unit(a.clone())],
            Box::new(Term::Unit(q.clone())),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[Q,a|Q]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Arg, 0),
                (Tag::Lis, 2),
                (Tag::Con, a_id),
                (Tag::Arg, 0),
                (Tag::Lis, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::List(
            vec![
                Term::List(vec![Term::Unit(Unit::Int(1)),Term::Unit(Unit::Int(2)),Term::Unit(Unit::Int(3))], Box::new(Term::EmptyList)),
                Term::EmptyList,
                Term::List(vec![Term::EmptyList], Box::new(Term::Unit(q.clone())))
            ],
            Box::new(Term::Unit(q.clone())),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), false);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[[1,2,3],[],[[]|Q]|Q]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Int, 1),
                (Tag::Lis, 2),
                (Tag::Int, 2),
                (Tag::Lis, 4),
                (Tag::Int, 3),
                EMPTY_LIS,
                EMPTY_LIS,
                (Tag::Arg, 0),
                (Tag::Lis, 0),
                (Tag::Lis,10),
                EMPTY_LIS,
                (Tag::Lis,12),
                (Tag::Lis, 6),
                (Tag::Arg, 0),
                (Tag::Lis, 8),
            ]
        );
        drop(heap.cells);
    }

    #[test]
    fn query_encode_list() {
        let mut heap = QueryHeap::new(Arc::new(Vec::new()),None);

        let _p_id = SymbolDB::set_const("p".into());
        let a_id = SymbolDB::set_const("a".into());
        let _f_id = SymbolDB::set_const("f".into());

        let _p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let _y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let _f = Unit::Constant("f".into());

        heap.cells = vec![];
        let term = Term::List(
            vec![
                Term::Unit(a.clone()),
                Term::Unit(x.clone()),
                Term::Unit(a.clone()),
            ],
            Box::new(Term::EmptyList),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[a,X,a]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Con, a_id),
                (Tag::Lis, 2),
                (Tag::Ref, 2),
                (Tag::Lis, 4),
                (Tag::Con, a_id),
                EMPTY_LIS,
                (Tag::Lis, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::List(
            vec![Term::Unit(q.clone()), Term::Unit(a.clone())],
            Box::new(Term::Unit(q.clone())),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[Q,a|Q]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Ref, 0),
                (Tag::Lis, 2),
                (Tag::Con, a_id),
                (Tag::Ref, 0),
                (Tag::Lis, 0),
            ]
        );

        heap.cells = vec![];
        let term = Term::List(
            vec![
                Term::List(vec![Term::Unit(Unit::Int(1)),Term::Unit(Unit::Int(2)),Term::Unit(Unit::Int(3))], Box::new(Term::EmptyList)),
                Term::EmptyList,
                Term::List(vec![Term::EmptyList], Box::new(Term::Unit(q.clone())))
            ],
            Box::new(Term::Unit(q.clone())),
        );
        let addr = term.encode(&mut heap.cells, &mut HashMap::new(), true);
        let addr = heap.heap_push((Tag::Lis, addr));
        assert_eq!(heap.cells.term_string(addr), "[[1,2,3],[],[[]|Q]|Q]");
        assert_eq!(
            heap.cells,
            [
                (Tag::Int, 1),
                (Tag::Lis, 2),
                (Tag::Int, 2),
                (Tag::Lis, 4),
                (Tag::Int, 3),
                EMPTY_LIS,
                EMPTY_LIS,
                (Tag::Ref, 7),
                (Tag::Lis, 0),
                (Tag::Lis,10),
                EMPTY_LIS,
                (Tag::Lis,12),
                (Tag::Lis, 6),
                (Tag::Ref, 7),
                (Tag::Lis, 8),
            ]
        );
        drop(heap.cells);
    }

}
