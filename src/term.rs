use std::{collections::HashMap, fmt, mem};
use fsize::fsize;
use crate::{
    heap::{Cell, Tag},
    Heap,
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
}

enum CellTerm {
    Cell(Cell),
    Term(Term),
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
        }
    }

    fn build_str(
        terms: &Box<[Term]>,
        heap: &mut Heap,
        var_ref: &mut HashMap<Box<str>, usize>,
    ) -> Cell {
        let terms: Vec<CellTerm> = terms
            .iter()
            .map(|t| t.build_to_cell(heap, var_ref))
            .collect();
        let addr = heap.len();
        heap.push((Tag::STR, terms.len() - 1));
        for term in terms {
            match term {
                CellTerm::Cell(cell) => heap.push(cell),
                CellTerm::Term(term) => {
                    term.build_on_heap(heap, var_ref);
                }
            }
        }
        (Tag::StrRef, addr)
    }

    fn build_lis(
        terms: &Vec<Term>,
        explicit_tail: bool,
        heap: &mut Heap,
        var_ref: &mut HashMap<Box<str>, usize>,
    ) -> Cell {
        let addr = heap.len();

        if terms.len() == 0 {
            heap.push(Heap::EMPTY_LIS)
        }

        let terms: Vec<CellTerm> = terms
            .iter()
            .map(|t| t.build_to_cell(heap, var_ref))
            .collect();
        for (i, term) in terms[..terms.len()].iter().enumerate() {
            match term {
                CellTerm::Cell(cell) => heap.push(*cell),
                CellTerm::Term(term) => {
                    term.build_on_heap(heap, var_ref);
                }
            }
            if i == terms.len() - 1 && !explicit_tail {
                heap.push(Heap::EMPTY_LIS)
            } else if i < terms.len() - 2 || !explicit_tail {
                heap.push((Tag::LIS, heap.len() + 1))
            }
        }

        (Tag::LIS, addr)
    }

    fn build_to_cell(&self, heap: &mut Heap, var_ref: &mut HashMap<Box<str>, usize>) -> CellTerm {
        match self {
            Term::FLT(value) => CellTerm::Cell((Tag::FLT, unsafe { mem::transmute_copy(value) })),
            Term::INT(value) => CellTerm::Cell((Tag::INT, unsafe { mem::transmute_copy(value) })),
            Term::VAR(symbol) => {
                if let Some(addr) = var_ref.get(symbol) {
                    CellTerm::Cell((Tag::REF, *addr))
                } else {
                    CellTerm::Term(Term::VAR(symbol.clone()))
                }
            }
            Term::VARUQ(symbol) => {
                if let Some(addr) = var_ref.get(symbol) {
                    CellTerm::Cell((Tag::REFA, *addr))
                } else {
                    CellTerm::Term(Term::VARUQ(symbol.clone()))
                }
            }
            Term::CON(symbol) => CellTerm::Cell((Tag::CON, heap.add_const_symbol(&symbol))),
            Term::LIS(terms, explicit_tail) => {
                CellTerm::Cell(Self::build_lis(terms, *explicit_tail, heap, var_ref))
            }
            Term::STR(terms) => CellTerm::Cell(Self::build_str(terms, heap, var_ref)),
        }
    }

    pub fn build_on_heap(&self, heap: &mut Heap, var_ref: &mut HashMap<Box<str>, usize>) -> usize {
        match self {
            Term::FLT(value) => {
                heap.push((Tag::FLT, unsafe { mem::transmute_copy(value) }));
                heap.len() - 1
            }
            Term::INT(value) => {
                heap.push((Tag::FLT, unsafe { mem::transmute_copy(value) }));
                heap.len() - 1
            }
            Term::VAR(symbol) => match var_ref.get(symbol) {
                Some(addr) => heap.set_var(Some(*addr), false),
                None => {
                    let addr = heap.set_var(None, false);
                    heap.symbols.set_var(&symbol, addr);
                    var_ref.insert(symbol.clone(), addr);
                    addr
                }
            },
            Term::VARUQ(symbol) => match var_ref.get(symbol) {
                Some(addr) => heap.set_var(Some(*addr), true),
                None => {
                    let addr = heap.set_var(None, true);
                    heap.symbols.set_var(&symbol, addr);
                    var_ref.insert(symbol.clone(), addr);
                    addr
                }
            },
            Term::CON(symbol) => {
                let id = heap.add_const_symbol(symbol);
                heap.set_const(id)
            }
            Term::LIS(terms, explicit_tail) => {
                Self::build_lis(terms, *explicit_tail, heap, var_ref).1
            }
            Term::STR(terms) => Self::build_str(terms, heap, var_ref).1,
        }
    }

    pub fn meta(&self) -> bool {
        match self {
            Term::FLT(_) | Term::INT(_) | Term::CON(_) | Term::VAR(_) => false,
            Term::VARUQ(_) => true,
            Term::LIS(sub_terms, _) => sub_terms.iter().any(|t| t.meta()),
            Term::STR(sub_terms) => {
                matches!(sub_terms[0], Term::VAR(_)) || sub_terms.iter().any(|t| t.meta())
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}