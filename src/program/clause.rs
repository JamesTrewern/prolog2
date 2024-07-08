use crate::heap::{
    heap::Heap, store::{Store, Tag}, symbol_db::SymbolDB
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
    pub fn to_string(&self, heap: &impl Heap) -> String {
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
    pub fn symbol_arity(&self, heap: &impl Heap) -> (usize, usize) {
        heap.str_symbol_arity(self[0])
    }

    /**Create symbols for the vars found in the clause
     * Used to make hypothesis easier to read
     */
    pub fn normalise(&self, heap: &mut impl Heap) {
        let mut args = Vec::<usize>::new();
        for literal in self.iter() {
            args.append(
                &mut heap
                    .term_vars(*literal)
                    .iter()
                    .filter_map(|(tag, addr)| if *tag == Tag::Arg { Some(*addr) } else { None })
                    .collect(),
            );
        }
        args.sort();
        args.dedup();

        for literal in self.iter(){
            heap.normalise_args(*literal, &args)
        }
    }

    pub fn equal(&self, other: &Self, self_heap: &impl Heap, other_heap: &impl Heap)-> bool{
        self.iter().zip(other.iter()).all(|(addr1,addr2)| self_heap.term_equal(*addr1, *addr2, other_heap))
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}
