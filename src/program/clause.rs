use crate::{
    heap::heap::{Heap, Tag},
    interface::term::Term,
};
use std::{collections::HashMap, mem::ManuallyDrop, ops::Deref};

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub(crate) enum ClauseType {
    CLAUSE,     //Simple 1st order clause
    BODY,       //1st order clause that can match with variable predicate symbol
    META,         //Higher-order clause
    HYPOTHESIS, //1st order clause that is generated during solving
}

pub struct Clause {
    pub clause_type: ClauseType,
    pub literals: ManuallyDrop<Box<[usize]>>, //Array of heap addresses pointing to clause literals
}

impl Clause {
    pub fn to_string(&self, heap: &Heap) -> String {
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
    pub fn symbol_arity(&self, heap: &Heap) -> (usize, usize) {
        heap.str_symbol_arity(self[0])
    }

    /**Take a vec of terms and build a clause on the heap*/
    pub fn parse_clause(terms: Vec<Term>, heap: &mut Heap) -> Clause {
        //Is any literal higher order?
        let clause_type = if terms.iter().any(|t| t.higher_order()) {
            ClauseType::META
        } else {
            ClauseType::CLAUSE
        };

        //Stores symbols and their addresses on the heap. 
        //Each symbol will insert a new k,v pair when it's first seen for this clause
        let mut var_ref = HashMap::new();

        //Build each term on the heap then collect the addresses into a boxed slice
        //Manually Drop is used because clauses built from the clause table are built from raw pointers
        let literals: ManuallyDrop<Box<[usize]>> = ManuallyDrop::new(terms
            .iter()
            .map(|t| t.build_on_heap(heap, &mut var_ref))
            .collect::<Box<[usize]>>());
        Clause { clause_type, literals}
    }

    /**Create symbols for the vars found in the clause
     * Used to make hypothesis easier to read
     */
    pub fn symbolise_vars(&self, heap: &mut Heap) {
        let mut vars = Vec::<usize>::new();
        for literal in self.iter() {
            vars.append(
                &mut heap
                    .term_vars(*literal)
                    .iter()
                    .filter_map(|(tag, addr)| if *tag == Tag::REFC { Some(*addr) } else { None })
                    .collect(),
            );
        }
        vars.sort();
        vars.dedup();

        let mut alphabet = (b'A'..=b'Z').map(|c| String::from_utf8(vec![c]).unwrap());
        for var in vars {
            let symbol = alphabet.next().unwrap();
            heap.symbols.set_var(&symbol, var);
        }
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}