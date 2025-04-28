use std::{cmp::Ordering, ops::Range};
use crate::heap::heap::Heap;
use super::predicate_table::SymbolArity;

enum ClauseMetaData<'a> {
    Clause(&'a [usize]),     // Literals range
    Meta(&'a [usize], u128), // Literals range, Existential variables bitflags
}

impl<'a> ClauseMetaData<'a> {
    pub fn literals(&self ) -> &'a [usize]{
        match self {
            ClauseMetaData::Clause(literals) => *literals,
            ClauseMetaData::Meta(literals, _) => *literals,
        }
    }

    pub fn head(&self ) -> usize{
        match self {
            ClauseMetaData::Clause(literals) => literals[0],
            ClauseMetaData::Meta(literals, _) => literals[0],
        }
    }
}

pub struct ClauseTable<'a> {
    clauses: Vec<ClauseMetaData<'a>>,
    litteral_addrs: Vec<usize>, //Heap addresses of clause literals
}

/**Given 2 clauses returns order between them
 * @c1: 1st clause
 * @c2: 2nd clause
 * @literals: The clause table's list of literal addresses
 * @heap: The heap
 */
fn order_clauses(
    c1: &ClauseMetaData,
    c2: &ClauseMetaData,
    literals: &[usize],
    heap: &impl Heap,
) -> Ordering {
    let symbol_arity1 = heap.str_symbol_arity(literals[c1.head()]);
    let symbol_arity2 = heap.str_symbol_arity(literals[c2.head()]);
    symbol_arity1.cmp(&symbol_arity2)
}

impl<'a> ClauseTable<'a> {

}

#[cfg(test)]
mod tests {

}