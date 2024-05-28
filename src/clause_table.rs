use std::{cmp::Ordering, collections::HashMap, ops::{Index, Range}};

use crate::{clause::*, Heap};

fn order_clauses(c1: &(ClauseType, usize, usize), c2: &(ClauseType, usize, usize)) -> Ordering {
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
    o1.cmp(&o2)
}

pub(crate) struct ClauseTable {
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

    pub fn len(&self) ->usize{
        self.clauses.len()
    }

    pub fn add_clause(&mut self, clause: Box<Clause>, clause_type: ClauseType) {
        self.clauses
            .push((clause_type, self.literal_addrs.len(), clause.len()));
        self.literal_addrs.extend_from_slice(&clause);
    }

    pub fn sort_clauses(&mut self) {
        self.clauses.sort_by(|c1, c2| order_clauses(c1, c2));
    }

    pub fn remove_clause(&mut self, i: usize) -> Box<Clause>{
        let (_, literals_ptr, clause_literals_len) = self.clauses.remove(i);
        assert!(
            self.literal_addrs.len() == literals_ptr + clause_literals_len,
            "Clause Not removed from top"
        );
        self.literal_addrs.drain(literals_ptr..literals_ptr+clause_literals_len).collect()
    }

    pub fn predicate_map(&self, heap: &Heap) -> HashMap<(usize, usize), Box<[usize]>> {
        let mut predicate_map = HashMap::<(usize, usize), Vec<usize>>::new();

        for idx in self.iter(&[ClauseType::CLAUSE, ClauseType::BODY]) {
            let (_,clause) = self.get(idx);
            let cell = heap.str_symbol_arity(clause[0]);
            if cell.0 >= isize::MAX as usize {
                match predicate_map.get_mut(&cell) {
                    Some(clauses) => clauses.push(idx),
                    None => {
                        predicate_map.insert(cell, vec![idx]);
                    }
                }
            }
        }


        predicate_map.into_iter().map(|(k,v)| (k,v.into_boxed_slice())).collect()
    }

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

    pub fn set_body(&mut self, i: usize){
        if let Some((clause_type,_,_)) = self.clauses.get_mut(i){
            *clause_type = ClauseType::BODY;
        }
    }

    //TO DO make types a &'static [ClauseType] array
    pub fn iter(&self, c_types: &[ClauseType]) -> impl Iterator<Item = usize> {
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

        ranges.into_iter().flat_map(|range| range)
    }

    pub fn get(&self, index: usize) -> (ClauseType, &Clause) {
        // if index >= self.clauses.len(){ return None;}
        let (ctype, literals_ptr, clause_literals_len) = self.clauses[index];
        let clause = &self.literal_addrs[literals_ptr..literals_ptr + clause_literals_len];
        (ctype, clause)
    }
}

impl<'a> Index<usize> for ClauseTable {
    type Output = [usize];

    fn index(&self, index: usize) -> &Self::Output {
        let (_, literals_ptr, clause_literals_len) = self.clauses[index];
        &self.literal_addrs[literals_ptr..literals_ptr + clause_literals_len]
    }
}

