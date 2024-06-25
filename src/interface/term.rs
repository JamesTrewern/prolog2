use crate::{
    heap::{
        store::{Cell, Store, Tag},
        symbol_db::SymbolDB,
    },
    program::clause::{Clause, ClauseType},
};
use fsize::fsize;
use std::{
    collections::HashMap,
    fmt,
    mem::{self, ManuallyDrop},
    ops::Deref,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    FLT(fsize),
    INT(isize),
    VAR(Box<str>),        //Symbol starting with uppercase
    VARUQ(Box<str>),      //Symbol starting with uppercase
    CON(Box<str>),        //Symbol starting with lowercase
    LIS(Vec<Term>, bool), //Terms, explicit tail?
    STR(Box<[Term]>),     //0th element is functor/predicate symbol, rest are arguments
    Cell(Cell),
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
            Term::LIS(terms, explicit_tail) => {
                format!(
                    "[{}]",
                    terms
                        .iter()
                        .enumerate()
                        .map(|(i, t)| if i == terms.len() - 1 {
                            format!("{t}")
                        } else if i == terms.len() - 2 && *explicit_tail {
                            format!("{t}| ")
                        } else {
                            format!("{t}, ")
                        })
                        .collect::<Vec<String>>()
                        .concat()
                )
            }
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
        }
    }
    
    fn build_str(
        terms: &Box<[Term]>,
        heap: &mut Store,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Cell {
        let terms: Vec<Term> = terms
            .iter()
            .map(|t| t.build_to_cell(heap, seen_vars, clause))
            .collect();
        let addr = heap.len();
        heap.push((Tag::Func, terms.len()));
        for term in terms {
            match term {
                Term::Cell(cell) => heap.push(cell),
                term => {
                    term.build_to_heap(heap, seen_vars, clause);
                }
            }
        }
        (Tag::Str, addr)
    }

    fn build_lis(
        terms: &Vec<Term>,
        explicit_tail: bool,
        heap: &mut Store,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Cell {
        let addr = heap.len();

        if terms.len() == 0 {
            return Store::EMPTY_LIS;
        }

        let terms: Vec<Term> = terms
            .iter()
            .map(|t| t.build_to_cell(heap, seen_vars, clause))
            .collect();
        for (i, term) in terms[..terms.len()].iter().enumerate() {
            match term {
                Term::Cell(cell) => heap.push(*cell),
                term => {
                    term.build_to_heap(heap, seen_vars, clause);
                }
            }
            if i == terms.len() - 1 && !explicit_tail {
                heap.push(Store::EMPTY_LIS)
            } else if i < terms.len() - 2 || !explicit_tail {
                heap.push((Tag::Lis, heap.len() + 1))
            }
        }

        (Tag::Lis, addr)
    }

    fn build_to_cell(
        &self,
        heap: &mut Store,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> Term {
        match self {
            Term::LIS(terms, explicit_tail) => Term::Cell(Self::build_lis(
                terms,
                *explicit_tail,
                heap,
                seen_vars,
                clause,
            )),
            Term::STR(terms) => Term::Cell(Self::build_str(terms, heap, seen_vars, clause)),
            _ => self.clone(),
        }
    }

    fn build_var(
        symbol: &str,
        heap: &mut Store,
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
        heap: &mut Store,
        seen_vars: &mut HashMap<Box<str>, usize>,
        clause: bool,
    ) -> usize {
        match self {
            Term::FLT(value) => {
                heap.push((Tag::Flt, unsafe { mem::transmute_copy(value) }));
                heap.len() - 1
            }
            Term::INT(value) => {
                heap.push((Tag::Int, unsafe { mem::transmute_copy(value) }));
                heap.len() - 1
            }
            Term::VAR(symbol) => Self::build_var(symbol, heap, seen_vars, false, clause),
            Term::VARUQ(symbol) => Self::build_var(symbol, heap, seen_vars, true, clause),
            Term::CON(symbol) => {
                let id = SymbolDB::set_const(symbol);
                heap.set_const(id)
            }
            Term::LIS(terms, explicit_tail) => {
                let cell = Self::build_lis(terms, *explicit_tail, heap, seen_vars, clause);
                heap.push(cell);
                heap.len() - 1
            }
            Term::STR(terms) => Self::build_str(terms, heap, seen_vars, clause).1,
            Term::Cell(cell) => {
                heap.push(*cell);
                heap.len() - 1
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
            Tag::Lis => Term::LIS(todo!(), todo!()),
            Tag::Arg | Tag::Ref => Term::VAR(match SymbolDB::get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::ArgA => Term::VARUQ(match SymbolDB::get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::Int => Term::INT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::Flt => Term::FLT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::Con => Term::CON(SymbolDB::get_const(heap[addr].1).into()),
        }
    }

}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

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

    pub fn to_heap(&self, heap: &mut Store) -> Clause {
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
