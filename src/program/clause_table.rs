use super::clause::{Clause, ClauseType};
use crate::heap::heap::Heap;
use std::{
    cmp::Ordering,
    collections::HashMap,
    mem::ManuallyDrop,
    ops::{Index, Range},
    ptr::slice_from_raw_parts,
};

/**Stores clauses as a list of adresses to literals on the heap
 * To prevent indirection and cache misses, the literal addresses are stored in a contigous block of memory
 * TO DO sort literal_addrs to match the order of clauses after usign sort clauses
 */
pub struct ClauseTable {
    pub clauses: Vec<(ClauseType, usize, usize)>,
    literal_addrs: Vec<usize>,
    pub type_flags: [usize; 4],
}

impl<'a> ClauseTable {
    const DEFAULT_CAPACITY: usize = 1000;

    pub fn new() -> ClauseTable {
        ClauseTable {
            clauses: vec![],
            literal_addrs: Vec::with_capacity(Self::DEFAULT_CAPACITY),
            type_flags: [0; 4],
        }
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /**Converts Clause object into flat representation in the clause table */
    pub fn add_clause(&mut self, mut clause: Clause) {
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
        heap: &Heap,
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
    pub fn sort_clauses(&mut self, heap: &Heap) {
        self.clauses
            .sort_by(|c1, c2| Self::order_clauses(c1, c2, &self.literal_addrs, heap));
    }

    pub fn remove_clause(&mut self, i: usize) {
        let (clause_type, literals_ptr, clause_literals_len) = self.clauses.remove(i);
        assert!(
            self.literal_addrs.len() == literals_ptr + clause_literals_len,
            "Clause Not removed from top"
        );
        let literals: Box<[usize]> = self
            .literal_addrs
            .drain(literals_ptr..literals_ptr + clause_literals_len)
            .collect();
    }

    /** Build a map from (symbol, arity) -> Range of indicies for clauses
     * This works as long as we sort the clause table
     */
    pub fn predicate_map(&self, heap: &Heap) -> HashMap<(usize, usize), Range<usize>> {
        let mut predicate_map = HashMap::<(usize, usize), (usize, usize)>::new();

        for idx in self.iter(&[ClauseType::CLAUSE, ClauseType::BODY]) {
            let clause = self.get(idx);
            let (symbol, arity) = heap.str_symbol_arity(clause[0]);
            match predicate_map.get_mut(&(symbol, arity)) {
                Some((start, len)) => *len += 1,
                None => {
                    predicate_map.insert((symbol, arity), (idx, 1));
                }
            }
        }

        predicate_map
            .into_iter()
            .map(|(k, v)| (k, v.0..v.0 + v.1))
            .collect()
    }

    /**Find the positions in the clause table where the clause type changes */
    pub fn find_flags(&mut self) {
        self.type_flags = [self.clauses.len(); 4];

        //TO DO analyse this, possibly incorrect logic
        for (i, (ct, _, _)) in self.clauses.iter().enumerate().rev() {
            match *ct {
                ClauseType::CLAUSE => {
                    self.type_flags[0] = i;
                }
                ClauseType::BODY => {
                    self.type_flags[1] = i;
                }
                ClauseType::META => {
                    self.type_flags[2] = i;
                }
                ClauseType::HYPOTHESIS => {
                    self.type_flags[3] = i;
                }
            }
        }

        for type_i in (0..3).rev() {
            if self.type_flags[type_i] > self.type_flags[type_i + 1] {
                self.type_flags[type_i] = self.type_flags[type_i + 1]
            }
        }
    }

    /**Set a clause to have the type BODY */
    pub fn set_body(&mut self, i: usize) {
        if let Some((clause_type, _, _)) = self.clauses.get_mut(i) {
            *clause_type = ClauseType::BODY;
        }
    }

    /**Creates an iterator over the clause indices that have a type within c_types
     * @c_types: array of the ClauseType enum determining which indices to iterate over
     */
    pub fn iter(&self, c_types: &[ClauseType]) -> ClauseIterator {
        let mut ranges = Vec::<Range<usize>>::new();

        if c_types.contains(&ClauseType::CLAUSE) {
            ranges.push(0..self.type_flags[1]);
        }
        if c_types.contains(&ClauseType::BODY) {
            ranges.push(self.type_flags[1]..self.type_flags[2]);
        }
        if c_types.contains(&ClauseType::META) {
            ranges.push(self.type_flags[2]..self.type_flags[3]);
        }
        if c_types.contains(&ClauseType::HYPOTHESIS) {
            ranges.push(self.type_flags[3]..self.len());
        }

        ClauseIterator { ranges }
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
}

impl<'a> Index<usize> for ClauseTable {
    type Output = [usize];

    fn index(&self, index: usize) -> &Self::Output {
        let (_, literals_ptr, clause_literals_len) = self.clauses[index];
        &self.literal_addrs[literals_ptr..literals_ptr + clause_literals_len]
    }
}

//TO DO rather than Vec of ranges make array[Option<Range>;4]
pub struct ClauseIterator {
    pub ranges: Vec<Range<usize>>,
}

impl Iterator for ClauseIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.ranges.last_mut().unwrap().next() {
            Some(i)
        } else {
            self.ranges.pop();
            if self.ranges.is_empty() {
                None
            } else {
                self.next()
            }
        }
    }
}
