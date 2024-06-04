use crate::{
    heap::heap::{Cell, Heap, Tag},
    program::clause::{self, Clause, ClauseType},
};
use fsize::fsize;
use std::{collections::HashMap, fmt, mem::{self, ManuallyDrop}, ops::Deref};

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
            return Heap::EMPTY_LIS;
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
                let cell = Self::build_lis(terms, *explicit_tail, heap, var_ref);
                heap.push(cell);
                heap.len() - 1
            }
            Term::STR(terms) => Self::build_str(terms, heap, var_ref).1,
        }
    }

    /**Create term object indepent of heap*/
    pub fn build_from_heap(addr: usize, heap: &Heap) -> Term {
        let addr = heap.deref_addr(addr);
        match heap[addr].0 {
            Tag::STR => Term::STR(
                heap.str_iterator(addr)
                    .map(|addr: usize| Self::build_from_heap(addr, heap))
                    .collect(),
            ),
            Tag::StrRef => Term::STR(
                heap.str_iterator(heap[addr].1)
                    .map(|addr: usize| Self::build_from_heap(addr, heap))
                    .collect(),
            ),
            Tag::LIS => Term::LIS(todo!(), todo!()),
            Tag::REFC | Tag::REF => Term::VAR(match heap.symbols.get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::REFA => Term::VARUQ(match heap.symbols.get_var(addr) {
                Some(symbol) => symbol.into(),
                None => format!("_{addr}").into(),
            }),
            Tag::INT => Term::INT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::FLT => Term::FLT(unsafe { mem::transmute(heap[addr].1) }),
            Tag::CON => Term::CON(heap.symbols.get_const(heap[addr].1).into()),
        }
    }

    pub fn higher_order(&self) -> bool {
        match self {
            Term::FLT(_) | Term::INT(_) | Term::CON(_) | Term::VAR(_) => false,
            Term::VARUQ(_) => true,
            Term::LIS(sub_terms, _) => sub_terms.iter().any(|t| t.higher_order()),
            Term::STR(sub_terms) => {
                matches!(sub_terms[0], Term::VAR(_)) || sub_terms.iter().any(|t| t.higher_order())
            }
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

    pub fn to_heap(&self, heap: &mut Heap) -> Clause {
        let clause_type = if self.meta {
            ClauseType::META
        } else {
            ClauseType::CLAUSE
        };

        //Stores symbols and their addresses on the heap.
        //Each symbol will insert a new k,v pair when it's first seen for this clause
        let mut var_ref = HashMap::new();

        //Build each term on the heap then collect the addresses into a boxed slice
        //Manually Drop is used because clauses built from the clause table are built from raw pointers
        let literals: ManuallyDrop<Box<[usize]>> = ManuallyDrop::new(
            self.literals
                .iter()
                .map(|t| t.build_on_heap(heap, &mut var_ref))
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
