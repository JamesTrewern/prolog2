use crate::heap::{
    store::{Store, Tag},
    symbol_db::SymbolDB,
};
use std::{mem::ManuallyDrop, ops::Deref};

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub(crate) enum ClauseType {
    CLAUSE,     //Simple 1st order clause
    BODY,       //1st order clause that can match with variable predicate symbol
    META,       //Higher-order clause
    HYPOTHESIS, //1st order clause that is generated during solving
}

pub struct Clause {
    pub clause_type: ClauseType,
    pub literals: ManuallyDrop<Box<[usize]>>, //Array of heap addresses pointing to clause literals
}

impl Clause {
    pub fn to_string(&self, heap: &Store) -> String {
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

    /**Get the symbol and arity of the head literal */
    pub fn symbol_arity(&self, heap: &Store) -> (usize, usize) {
        heap.str_symbol_arity(self[0])
    }

    /**Create symbols for the vars found in the clause
     * Used to make hypothesis easier to read
     */
    pub fn symbolise_vars(&self, heap: &mut Store) {
        let mut vars = Vec::<usize>::new();
        for literal in self.iter() {
            vars.append(
                &mut heap
                    .term_vars(*literal)
                    .iter()
                    .filter_map(|(tag, addr)| if *tag == Tag::Arg { Some(*addr) } else { None })
                    .collect(),
            );
        }
        vars.sort();
        vars.dedup();

        let mut alphabet = (b'A'..=b'Z').map(|c| String::from_utf8(vec![c]).unwrap());
        for var in vars {
            let symbol = alphabet.next().unwrap();
            SymbolDB::set_var(&symbol, var);
        }
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}
