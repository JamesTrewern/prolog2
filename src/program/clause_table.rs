use std::{cmp::Ordering, ops::Range};
use crate::heap::heap::Heap;
use super::predicate_table::SymbolArity;

enum ClauseMetaData {
    Clause((usize,usize)),     // Literals range
    Meta((usize,usize), u128), // Literals range, Existential variables bitflags
}

impl ClauseMetaData {
    pub fn literals(&self ) -> Range<usize>{
        match self {
            ClauseMetaData::Clause(range) => range.0 .. range.1,
            ClauseMetaData::Meta(range, _) => range.0 .. range.1,
        }
    }

    pub fn head(&self ) -> usize{
        match self {
            ClauseMetaData::Clause(range) => range.0,
            ClauseMetaData::Meta(range, _) => range.0,
        }
    }
}

pub struct ClauseTable {
    clauses: Vec<ClauseMetaData>,
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

impl ClauseTable {}

#[cfg(test)]
mod tests {

}