use std::{collections::HashMap, mem};

use super::{build_tree::Clause, term::{Term, Unit}};
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


