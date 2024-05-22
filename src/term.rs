use std::{collections::HashMap, fmt};

use fsize::fsize;

use crate::Heap;

#[derive(Debug, PartialEq)]
pub enum Term {
    FLT(fsize),
    INT(isize),
    VAR(Box<str>),          //Symbol starting with uppercase
    VARUQ(Box<str>),          //Symbol starting with uppercase
    CON(Box<str>),          //Symbol starting with lowercase
    LIS(Vec<Term>, bool), //Terms, explicit tail?
    STR(Box<[Term]>),         //0th element is functor/predicate symbol, rest are arguments
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
                let len = terms.len();
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

    pub fn vars(&self) -> Vec<usize>{
        todo!()
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
