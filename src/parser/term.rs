use std::{collections::HashMap, mem};

use fsize::fsize;

use crate::heap::{Heap, SymbolDB, Tag, EMPTY_LIS, LIS};

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord)]
pub enum Str {
    Comp,
    Tup,
    Set,
}

impl Str {
    fn tag(&self) -> Tag {
        match self {
            Self::Comp => Tag::Comp,
            Self::Tup => Tag::Tup,
            Self::Set => Tag::Set,
        }
    }
}

#[derive(Debug, PartialEq, Clone, PartialOrd)]
pub enum Term {
    Str(Str, Vec<Term>),
    List(Vec<Term>, Box<Term>),
    EmptyList,
    EmptySet,
    Constant(String),
    Variable(String),
    Int(isize),
    Float(fsize),
    String(String),
    AnonVar,
}

impl Term {
    pub fn parse_unit(token: &str) -> Option<Self> {
        let c = token.chars().next()?;
        match c {
            '\'' => Some(Term::Constant(token[1..token.len() - 1].into())),
            '"' => Some(Term::String(token[1..token.len() - 1].into())),
            '_' => Some(Term::AnonVar),
            c if c.is_lowercase() => Some(Term::Constant(token.into())),
            c if c.is_uppercase() => Some(Term::Variable(token.into())),
            c if c == '-' || c.is_numeric() => {
                if let Ok(num) = token.parse::<isize>() {
                    Some(Term::Int(num))
                } else if let Ok(num) = token.parse::<fsize>() {
                    Some(Term::Float(num))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Convenience wrapper function for encode, returns address of new term
    /// Helps to maintian old code
    pub fn encode(
        self,
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) -> usize {
        let addr = heap.heap_len();
        self.encode_rec(heap, var_values, query);
        addr
    }

    pub fn encode_rec(
        self,
        heap: &mut impl Heap,
        var_values: &mut HashMap<String, usize>,
        query: bool,
    ) {
        match self {
            Term::List(head, tail) => encode_list(head, *tail, heap, var_values, query),
            Term::Str(str_type, terms) => encode_struct(str_type, terms, heap, var_values, query),
            Term::EmptyList => _ = heap.heap_push(EMPTY_LIS),
            Term::EmptySet => _ = heap.heap_push((Tag::Set, 0)),
            Term::Constant(symbol) => {
                let id = SymbolDB::set_const(symbol.clone());
                heap.heap_push((Tag::Con, id));
            }
            Term::Variable(symbol) => encode_var(symbol, heap, var_values, query),
            Term::Int(value) => {
                heap.heap_push((Tag::Int, unsafe { mem::transmute_copy(&value) }));
            }
            Term::Float(value) => {
                heap.heap_push((Tag::Flt, unsafe { mem::transmute_copy(&value) }));
            }
            Term::String(text) => {
                let str_id = SymbolDB::set_string(text.clone());
                heap.heap_push((Tag::Stri, str_id));
            }
            Term::AnonVar => _ = heap.heap_push((Tag::AVar, 0)),
        }
    }
}

fn encode_var(
    symbol: String,
    heap: &mut impl Heap,
    var_values: &mut HashMap<String, usize>,
    query: bool,
) {
    match var_values.get(&symbol) {
        Some(ref_addr) if query => _ = heap.heap_push((Tag::Ref, *ref_addr)),
        Some(arg) => {
            let addr = heap.heap_push((Tag::Arg, *arg));
            SymbolDB::set_var(symbol, addr, heap.get_id(addr));
        }
        None if query => {
            let addr = heap.set_var(None);
            var_values.insert(symbol.clone(), addr);
            SymbolDB::set_var(symbol, addr, heap.get_id(addr));
        }
        None => {
            let v = var_values.len();
            var_values.insert(symbol.clone(), v);
            let addr = heap.heap_push((Tag::Arg, v));
            SymbolDB::set_var(symbol, addr, heap.get_id(addr));
        }
    }
}

fn encode_struct(
    str_type: Str,
    mut terms: Vec<Term>,
    heap: &mut impl Heap,
    var_values: &mut HashMap<String, usize>,
    query: bool,
) {
    if str_type == Str::Set {
        terms.sort_by(|a, b| a.partial_cmp(b).unwrap());
        terms.dedup();
    }
    heap.heap_push((str_type.tag(), terms.len()));
    for term in terms {
        term.encode_rec(heap, var_values, query);
    }
}

fn encode_list(
    head: Vec<Term>,
    tail: Term,
    heap: &mut impl Heap,
    var_values: &mut HashMap<String, usize>,
    query: bool,
) {
    for term in head {
        heap.heap_push(LIS);
        term.encode_rec(heap, var_values, query);
    }
    tail.encode_rec(heap, var_values, query);
}

#[cfg(test)]
mod encode_tests {
    use std::collections::HashMap;

    use super::Term;
    use crate::{
        heap::{Heap, QueryHeap, SymbolDB, Tag, EMPTY_LIS, LIS},
        parser::term::Str,
    };

    use fsize::fsize;

    #[test]
    fn encode_argument() {
        let mut heap = QueryHeap::new(&[], None);
        let mut var_values = HashMap::new();
        let x = Term::Variable("X".into());
        let y = Term::Variable("Y".into());
        x.clone().encode(&mut heap, &mut var_values, false);
        y.clone().encode(&mut heap, &mut var_values, false);
        x.encode(&mut heap, &mut var_values, false);
        y.encode(&mut heap, &mut var_values, false);

        assert_eq!(
            heap.cells,
            [(Tag::Arg, 0), (Tag::Arg, 1), (Tag::Arg, 0), (Tag::Arg, 1),]
        );
    }

    #[test]
    fn encode_ref() {
        let mut heap = QueryHeap::new(&[], None);
        let mut var_values = HashMap::new();
        let x = Term::Variable("X".into());
        let y = Term::Variable("Y".into());
        x.clone().encode(&mut heap, &mut var_values, true);
        y.clone().encode(&mut heap, &mut var_values, true);
        x.encode(&mut heap, &mut var_values, true);
        y.encode(&mut heap, &mut var_values, true);

        assert_eq!(
            heap.cells,
            [(Tag::Ref, 0), (Tag::Ref, 1), (Tag::Ref, 0), (Tag::Ref, 1),]
        );
    }

    #[test]
    fn encode_unit() {
        let a = SymbolDB::set_const("a");

        let mut heap = QueryHeap::new(&[], None);
        let unit = Term::Constant("a".into());
        let addr = unit.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "a");
        assert_eq!(heap.cells, [(Tag::Con, a)]);

        let mut heap = QueryHeap::new(&[], None);
        let unit = Term::Int(10);
        let addr = unit.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "10");
        assert_eq!(heap.cells, [(Tag::Int, 10)]);

        let mut heap = QueryHeap::new(&[], None);
        let value: isize = -10;
        let unit = Term::Int(value);
        let addr = unit.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "-10");
        assert_eq!(heap.cells, [(Tag::Int, isize::cast_unsigned(value))]);

        let mut heap = QueryHeap::new(&[], None);
        let value: fsize = 1.1;
        let unit = Term::Float(value);
        let addr = unit.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "1.1");

        #[cfg(target_pointer_width = "32")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        #[cfg(target_pointer_width = "64")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        let mut heap = QueryHeap::new(&[], None);
        let value: fsize = -1.1;
        let unit = Term::Float(value);
        let addr = unit.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "-1.1");

        #[cfg(target_pointer_width = "32")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);

        #[cfg(target_pointer_width = "64")]
        assert_eq!(heap.cells, [(Tag::Flt, value.to_bits() as usize)]);
    }

    #[test]
    fn program_encode_compound() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Comp, vec![p.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        SymbolDB::_see_var_map();
        assert_eq!(heap.term_string(addr), "p(X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Comp, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "Q(a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        term.encode(&mut heap, &mut HashMap::new(), false);
        // assert_eq!(heap.term_string(addr), "p(f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        term.encode(&mut heap, &mut HashMap::new(), false);
        // assert_eq!(heap.term_string(addr), "p((f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        term.encode(&mut heap, &mut HashMap::new(), false);
        // assert_eq!(heap.term_string(addr), "p({f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        term.encode(&mut heap, &mut HashMap::new(), false);
        // assert_eq!(heap.term_string(addr), "p([f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Lis, 0),
                (Tag::Con, f_id),
                (Tag::Lis, 0),
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Arg, 0),
            ]
        );
    }

    #[test]
    fn query_encode_compound() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Comp, vec![p.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "p(X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 2),
                (Tag::Con, a_id),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Comp, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "Q(a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Ref, 1),
                (Tag::Con, a_id),
                (Tag::Ref, 1),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "p(f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "p((f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "p({f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Comp,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "p([f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Comp, 3),
                (Tag::Con, p_id),
                LIS,
                (Tag::Con, f_id),
                LIS,
                (Tag::Ref, 5),
                EMPTY_LIS,
                (Tag::Ref, 5),
            ]
        );
    }

    #[test]
    fn program_encode_tuple() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Tup, vec![p.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(p,X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Tup, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(Q,a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Arg, 0),
                (Tag::Con, a_id),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(p,f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(p,(f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(p,{f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "(p,[f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                LIS,
                (Tag::Con, f_id),
                LIS,
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Arg, 0),
            ]
        );
    }

    #[test]
    fn query_encode_tuple() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Tup, vec![p.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(p,X,a)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 2),
                (Tag::Con, a_id),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Tup, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(Q,a,Q)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Ref, 1),
                (Tag::Con, a_id),
                (Tag::Ref, 1),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(p,f(X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(p,(f,X),X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(p,{f,X},X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 4),
                (Tag::Ref, 4),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Tup,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "(p,[f,X],X)");
        assert_eq!(
            heap.cells,
            [
                (Tag::Tup, 3),
                (Tag::Con, p_id),
                LIS,
                (Tag::Con, f_id),
                LIS,
                (Tag::Ref, 5),
                EMPTY_LIS,
                (Tag::Ref, 5),
            ]
        );
    }

    #[test]
    fn program_encode_set() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Set, vec![a.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{a,X}");
        assert_eq!(
            heap.cells,
            [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Arg, 0),]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Set, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{a,Q}");
        assert_eq!(heap.cells, [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Arg, 0)]);

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{f(X),p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{(f,X),p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{{f,X},p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Arg, 0),
                (Tag::Con, p_id),
                (Tag::Arg, 0),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "{[f,X],p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                LIS,
                (Tag::Con, f_id),
                LIS,
                (Tag::Arg, 0),
                EMPTY_LIS,
                (Tag::Con, p_id),
                (Tag::Arg, 0),
            ]
        );
    }

    #[test]
    fn query_encode_set() {
        let p_id = SymbolDB::set_const("p");
        let a_id = SymbolDB::set_const("a");
        let f_id = SymbolDB::set_const("f");

        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let f = Term::Constant("f".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Set, vec![a.clone(), x.clone(), a.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{a,X}");
        assert_eq!(
            heap.cells,
            [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Ref, 2),]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(Str::Set, vec![q.clone(), a.clone(), q.clone()]);
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{a,Q}");
        assert_eq!(
            heap.cells,
            [(Tag::Set, 2), (Tag::Con, a_id), (Tag::Ref, 2),]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Comp, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{f(X),p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Comp, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 3),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Tup, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{(f,X),p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Tup, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 3),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::Str(Str::Set, vec![f.clone(), x.clone()]),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{{f,X},p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                (Tag::Set, 2),
                (Tag::Con, f_id),
                (Tag::Ref, 3),
                (Tag::Con, p_id),
                (Tag::Ref, 3),
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::Str(
            Str::Set,
            vec![
                p.clone(),
                Term::List(vec![f.clone(), x.clone()], Box::new(Term::EmptyList)),
                x.clone(),
            ],
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "{[f,X],p,X}");
        assert_eq!(
            heap.cells,
            [
                (Tag::Set, 3),
                LIS,
                (Tag::Con, f_id),
                LIS,
                (Tag::Ref, 4),
                EMPTY_LIS,
                (Tag::Con, p_id),
                (Tag::Ref, 4),
            ]
        );
    }

    #[test]
    fn program_encode_list() {
        let a_id = SymbolDB::set_const("a");

        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let a = Term::Constant("a".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(
            vec![a.clone(), x.clone(), a.clone()],
            Box::new(Term::EmptyList),
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "[a,X,a]");
        assert_eq!(
            heap.cells,
            [
                LIS,
                (Tag::Con, a_id),
                LIS,
                (Tag::Arg, 0),
                LIS,
                (Tag::Con, a_id),
                EMPTY_LIS,
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(vec![q.clone(), a.clone()], Box::new(q.clone()));
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "[Q,a|Q]");
        assert_eq!(
            heap.cells,
            [LIS, (Tag::Arg, 0), LIS, (Tag::Con, a_id), (Tag::Arg, 0),]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(
            vec![
                Term::List(
                    vec![Term::Int(1), Term::Int(2), Term::Int(3)],
                    Box::new(Term::EmptyList),
                ),
                Term::EmptyList,
                Term::List(vec![Term::EmptyList], Box::new(q.clone())),
            ],
            Box::new(q.clone()),
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), false);
        assert_eq!(heap.term_string(addr), "[[1,2,3],[],[[]|Q]|Q]");
        assert_eq!(
            heap.cells,
            [
                LIS,
                LIS,
                (Tag::Int, 1),
                LIS,
                (Tag::Int, 2),
                LIS,
                (Tag::Int, 3),
                EMPTY_LIS,
                LIS,
                EMPTY_LIS,
                LIS,
                LIS,
                EMPTY_LIS,
                (Tag::Arg, 0),
                (Tag::Arg, 0),
            ]
        );
    }

    #[test]
    fn query_encode_list() {
        let a_id = SymbolDB::set_const("a");

        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let a = Term::Constant("a".into());

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(
            vec![a.clone(), x.clone(), a.clone()],
            Box::new(Term::EmptyList),
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "[a,X,a]");
        assert_eq!(
            heap.cells,
            [
                LIS,
                (Tag::Con, a_id),
                LIS,
                (Tag::Ref, 3),
                LIS,
                (Tag::Con, a_id),
                EMPTY_LIS,
            ]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(vec![q.clone(), a.clone()], Box::new(q.clone()));
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "[Q,a|Q]");
        assert_eq!(
            heap.cells,
            [LIS, (Tag::Ref, 1), LIS, (Tag::Con, a_id), (Tag::Ref, 1),]
        );

        let mut heap = QueryHeap::new(&[], None);
        let term = Term::List(
            vec![
                Term::List(
                    vec![Term::Int(1), Term::Int(2), Term::Int(3)],
                    Box::new(Term::EmptyList),
                ),
                Term::EmptyList,
                Term::List(vec![Term::EmptyList], Box::new(q.clone())),
            ],
            Box::new(q.clone()),
        );
        let addr = term.encode(&mut heap, &mut HashMap::new(), true);
        assert_eq!(heap.term_string(addr), "[[1,2,3],[],[[]|Q]|Q]");
        assert_eq!(
            heap.cells,
            [
                LIS,
                LIS,
                (Tag::Int, 1),
                LIS,
                (Tag::Int, 2),
                LIS,
                (Tag::Int, 3),
                EMPTY_LIS,
                LIS,
                EMPTY_LIS,
                LIS,
                LIS,
                EMPTY_LIS,
                (Tag::Ref, 13),
                (Tag::Ref, 13),
            ]
        );
    }
}
