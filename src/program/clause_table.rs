use super::clause::{Clause, ClauseType};
use crate::heap::{self, heap::Heap};
use std::{cmp::Ordering, mem::ManuallyDrop, ops::Index, ptr::slice_from_raw_parts};

/**Stores clauses as a list of adresses to literals on the heap
 * To prevent indirection and cache misses, the literal addresses are stored in a contigous block of memory
 * TO DO sort literal_addrs to match the order of clauses after usign sort clauses
 */
#[derive(Clone)]
pub struct ClauseTable {
    clauses: Vec<(ClauseType, usize, usize)>,
    literal_addrs: Vec<usize>,
}

impl<'a> ClauseTable {
    const DEFAULT_CAPACITY: usize = 1000;

    pub fn new() -> ClauseTable {
        ClauseTable {
            clauses: vec![],
            literal_addrs: Vec::with_capacity(Self::DEFAULT_CAPACITY),
        }
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /**Converts Clause object into flat representation in the clause table */
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses
            .push((clause.clause_type, self.literal_addrs.len(), clause.len()));

        //To allow Box to be dropped we must take out the inner value so it can fall out of scope and call destructor
        let literals = ManuallyDrop::into_inner(clause.literals);
        self.literal_addrs.extend_from_slice(&literals);
    }

    /**Given 2 clauses returns order between them
     * @c1: 1st clause
     * @c2: 2nd clause
     * @literals: The clause table's list of literal addresses
     * @heap: The heap
     */
    fn order_clauses(
        c1: &(ClauseType, usize, usize),
        c2: &(ClauseType, usize, usize),
        literals: &[usize],
        heap: &impl Heap,
    ) -> Ordering {
        let o1 = match c1.0 {
            ClauseType::CLAUSE => 1,
            ClauseType::BODY => 2,
            ClauseType::META => 3,
            ClauseType::HYPOTHESIS => 4,
        };
        let o2 = match c2.0 {
            ClauseType::CLAUSE => 1,
            ClauseType::BODY => 2,
            ClauseType::META => 3,
            ClauseType::HYPOTHESIS => 4,
        };
        //Does the clause Type match, if so order by symbol
        match o1.cmp(&o2) {
            Ordering::Equal => {
                let (symbol1, arity1) = heap.str_symbol_arity(literals[c1.1]);
                let (symbol2, arity2) = heap.str_symbol_arity(literals[c2.1]);
                //Are the symbols the same, if so order by arity
                match symbol1.cmp(&symbol2) {
                    Ordering::Equal => arity1.cmp(&arity2),
                    v => v,
                }
            }
            v => v,
        }
    }

    /**sort the clauses using the order clauses funtion */
    pub fn sort_clauses(&mut self, heap: &impl Heap) {
        self.clauses
            .sort_by(|c1, c2| Self::order_clauses(c1, c2, &self.literal_addrs, heap));
    }

    pub fn remove_clause(&mut self, i: usize) -> Clause {
        let (clause_type, literals_ptr, clause_literals_len) = self.clauses.remove(i);
        assert!(
            self.literal_addrs.len() == literals_ptr + clause_literals_len,
            "Clause Not removed from top"
        );
        let literals = ManuallyDrop::new(
            self.literal_addrs
                .drain(literals_ptr..literals_ptr + clause_literals_len)
                .collect::<Box<[usize]>>(),
        );
        Clause {
            clause_type,
            literals,
        }
    }

    /**Find the positions in the clause table where the clause type changes */
    pub fn find_flags(&mut self) -> [usize; 4] {
        let mut type_flags = [self.clauses.len(); 4];
        //TO DO analyse this, possibly incorrect logic
        for (i, (ct, _, _)) in self.clauses.iter().enumerate().rev() {
            match *ct {
                ClauseType::CLAUSE => {
                    type_flags[0] = i;
                }
                ClauseType::BODY => {
                    type_flags[1] = i;
                }
                ClauseType::META => {
                    type_flags[2] = i;
                }
                ClauseType::HYPOTHESIS => {
                    type_flags[3] = i;
                }
            }
        }
        for type_i in (0..3).rev() {
            if type_flags[type_i] > type_flags[type_i + 1] {
                type_flags[type_i] = type_flags[type_i + 1]
            }
        }
        type_flags
    }

    /**Set a clause to have the type BODY */
    pub fn set_body(&mut self, i: usize) {
        if let Some((clause_type, _, _)) = self.clauses.get_mut(i) {
            *clause_type = ClauseType::BODY;
        }
    }

    /**Create Boxed Sliced containing the heap addressses of the clause literals then constructs a new clause object using this */
    pub fn get(&self, index: usize) -> Clause {
        let (clause_type, literals_ptr, clause_literals_len) = self.clauses[index];

        //Construct a fat pointer to the slice holding the literal addresses
        let p = slice_from_raw_parts(
            unsafe { self.literal_addrs.as_ptr().add(literals_ptr) },
            clause_literals_len,
        ) as *mut [usize];

        //Wrap in manually drop so the clause falling out of scope does not deallocate memory
        let literals = unsafe { ManuallyDrop::new(Box::from_raw(p)) };

        Clause {
            clause_type,
            literals,
        }
    }

    pub fn iter(&self) -> ClauseIterator {
        ClauseIterator {
            index: 0,
            clause_table: self,
        }
    }

    pub fn equal(&self, other: &Self, self_heap: &impl Heap, other_heap: &impl Heap) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for c1 in self.iter() {
            if !other.iter().any(|c2| c1.equal(&c2, self_heap, other_heap)) {
                return false;
            }
        }
        true
    }

    pub fn add_offset(&mut self, offset: usize){
        for literal_addr in self.literal_addrs.iter_mut(){
            *literal_addr += offset;
        }
    }
}

impl<'a> Index<usize> for ClauseTable {
    type Output = [usize];

    fn index(&self, index: usize) -> &Self::Output {
        let (_, literals_ptr, clause_literals_len) = self.clauses[index];
        &self.literal_addrs[literals_ptr..literals_ptr + clause_literals_len]
    }
}

//TO DO rather than Vec of ranges make array[Option<Range>;4]
pub struct ClauseIterator<'a> {
    index: usize,
    clause_table: &'a ClauseTable,
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = Clause;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.clause_table.len() {
            let res = Some(self.clause_table.get(self.index));
            self.index += 1;
            res
        } else {
            None
        }
    }
}
