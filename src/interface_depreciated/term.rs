use crate::{
    heap::{
        heap::Heap,
        store::{Cell, Store, Tag},
        symbol_db::SymbolDB,
    },
    program::clause::{Clause, ClauseType},
};
use fsize::fsize;
use std::{
    collections::HashMap, fmt, hash::Hash, mem::{self, ManuallyDrop}, ops::Deref, sync::Arc
};

const VAR_SYMBOLS: [&str; 26] = [
    "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S",
    "T", "U", "V", "W", "X", "Y", "Z",
];

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    FLT(fsize),
    INT(isize),
    VAR(Arc<str>),             //Symbol starting with uppercase
    VARUQ(Arc<str>),           //Symbol starting with uppercase
    CON(Arc<str>),             //Symbol starting with lowercase
    LIS(Box<Term>, Box<Term>), //Terms, explicit tail?
    STR(Box<[Term]>),          //0th element is functor/predicate symbol, rest are arguments
    Cell(Cell),
    EMPTY_LIS,
}

impl Term {
    pub fn symbol(&self) -> &str {
        match self {
            Term::VAR(symbol) => symbol,
            Term::CON(symbol) => symbol,
            _ => panic!(),
        }
    }

    fn to_string(&self) -> String {
        match self {
            Term::FLT(value) => value.to_string(),
            Term::INT(value) => value.to_string(),
            Term::VAR(symbol) => symbol.to_string(),
            Term::VARUQ(symbol) => symbol.to_string(),
            Term::CON(symbol) => symbol.to_string(),
            Term::LIS(head, tail) => format!("[{head}, {tail}]"),
            Term::STR(terms) => {
                let mut buf = String::new();
                buf += &terms[0].to_string();
                buf += "(";
                for term in &terms[1..] {
                    buf += &term.to_string();
                    buf += ",";
                }
                buf.pop();
                buf += ")";
                buf
            }
            Term::Cell(_) => todo!(),
            Term::EMPTY_LIS => "[]".into(),
        }
    }

    fn build_str(
        terms: &Box<[Term]>,
        heap: &mut impl Heap,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Cell {
        let terms: Vec<Term> = terms
            .iter()
            .map(|t| t.build_to_cell(heap, seen_vars, clause))
            .collect();
        let addr = heap.heap_len();
        heap.heap_push((Tag::Func, terms.len()));
        for term in terms {
            match term {
                Term::Cell(cell) => heap.heap_push(cell),
                term => {
                    term.build_to_heap(heap, seen_vars, clause);
                }
            }
        }
        (Tag::Str, addr)
    }

    fn build_lis(
        head: &Term,
        tail: &Term,
        heap: &mut impl Heap,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Cell {
        let tail = tail.build_to_cell(heap, seen_vars, clause);
        let head = head.build_to_cell(heap, seen_vars, clause);

        let addr = heap.heap_len();

        head.build_to_heap(heap, seen_vars, clause);
        tail.build_to_heap(heap, seen_vars, clause);

        (Tag::Lis, addr)
    }

    fn build_to_cell(
        &self,
        heap: &mut impl Heap,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Term {
        match self {
            Term::LIS(head, tail) => {
                Term::Cell(Self::build_lis(head, tail, heap, seen_vars, clause))
            }
            Term::STR(terms) => Term::Cell(Self::build_str(terms, heap, seen_vars, clause)),
            _ => self.clone(),
        }
    }

    fn build_var(
        symbol: &str,
        heap: &mut impl Heap,
        seen_vars: &mut HashMap<Box<str>, usize>,
        ho: bool,
        clause: bool,
    ) -> usize {
        if clause {
            match seen_vars.get(symbol) {
                Some(value) => heap.set_arg(*value, ho),
                None => {
                    let value = seen_vars.len();
                    let addr = heap.set_arg(value, ho);
                    SymbolDB::set_var(&symbol, addr);
                    seen_vars.insert(symbol.into(), value);
                    addr
                }
            }
        } else {
            match seen_vars.get(symbol) {
                Some(addr) => heap.set_ref(Some(*addr)),
                None => {
                    let addr = heap.set_ref(None);
                    SymbolDB::set_var(&symbol, addr);
                    seen_vars.insert(symbol.into(), addr);
                    addr
                }
            }
        }
    }

    pub fn build_to_heap(
        &self,
        heap: &mut impl Heap,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> usize {
        match self {
            Term::FLT(value) => {
                heap.heap_push((Tag::Flt, unsafe { mem::transmute_copy(value) }));
                heap.heap_len() - 1
            }
            Term::INT(value) => {
                heap.heap_push((Tag::Int, unsafe { mem::transmute_copy(value) }));
                heap.heap_len() - 1
            }
            Term::VAR(symbol) => Self::build_var(symbol, heap, seen_vars, false, clause),
            Term::VARUQ(symbol) => Self::build_var(symbol, heap, seen_vars, true, clause),
            Term::CON(symbol) => {
                let id = SymbolDB::set_const(symbol);
                heap.set_const(id)
            }
            Term::LIS(head, tail) => {
                let cell = Self::build_lis(head, tail, heap, seen_vars, clause);
                heap.heap_push(cell);
                heap.heap_len() - 1
            }
            Term::STR(terms) => Self::build_str(terms, heap, seen_vars, clause).1,
            Term::Cell(cell) => {
                heap.heap_push(*cell);
                heap.heap_len() - 1
            }
            Term::EMPTY_LIS => {
                heap.heap_push(Store::EMPTY_LIS);
                heap.heap_len() - 1
            }
        }
    }

    /**Create term object indepent of heap*/
    pub fn build_from_heap(addr: usize, heap: &Store) -> Term {
        let addr = heap.deref_addr(addr);
        match heap[addr].0 {
            Tag::Func => Term::STR(
                heap.str_iterator(addr)
                    .map(|addr: usize| Self::build_from_heap(addr, heap))
                    .collect(),
            ),
            Tag::Str => Term::STR(
                heap.str_iterator(heap[addr].1)
                    .map(|addr: usize| Self::build_from_heap(addr, heap))
                    .collect(),
            ),
            Tag::Lis if heap[addr] == Store::EMPTY_LIS => Term::EMPTY_LIS,
            Tag::Lis => Term::LIS(
                Self::build_from_heap(heap[addr].1, heap).into(),
                Self::build_from_heap(heap[addr].1 + 1, heap).into(),
            ),
            Tag::Arg | Tag::Ref => Term::VAR(VAR_SYMBOLS[heap[addr].1].into()),
            Tag::ArgA => Term::VARUQ(VAR_SYMBOLS[heap[addr].1].into()),
            Tag::Int => Term::INT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::Flt => Term::FLT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::Con => Term::CON(SymbolDB::get_const(heap[addr].1).into()),
        }
    }

    pub fn list_from_slice(terms: &[Term]) -> Term {
        let mut tail = Term::EMPTY_LIS;
        for term in terms.iter().rev() {
            tail = Term::LIS(term.clone().into(), tail.into())
        }
        tail
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
#[derive(PartialEq, Eq)]
pub struct TermClause {
    pub literals: Vec<Term>,
    pub meta: bool,
}

impl TermClause {
    pub fn to_string(&self) -> String {
        if self.literals.len() == 1 {
            format!("{}.", self.literals[0])
        } else {
            let mut body = self.literals[1..]
                .iter()
                .map(|literal| format!("{literal},"))
                .collect::<Vec<String>>()
                .concat();
            body.pop();
            body += ".";
            format!("{}:-{body}", self.literals[0])
        }
    }

    pub fn to_heap(&self, heap: &mut impl Heap) -> Clause {
        let clause_type = if self.meta {
            ClauseType::META
        } else {
            ClauseType::CLAUSE
        };

        //Stores symbols and their addresses on the heap.
        //Each symbol will insert a new k,v pair when it's first seen for this clause
        let mut seen_vars = HashMap::new();

        //Build each term on the heap then collect the addresses into a boxed slice
        //Manually Drop is used because clauses built from the clause table are built from raw pointers
        let literals: ManuallyDrop<Box<[usize]>> = ManuallyDrop::new(
            self.literals
                .iter()
                .map(|t| t.build_to_heap(heap, &mut seen_vars, true))
                .collect::<Box<[usize]>>(),
        );
        Clause {
            clause_type,
            literals,
        }
    }
}

impl fmt::Display for TermClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Deref for TermClause {
    type Target = [Term];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}

impl Eq for Term{}
