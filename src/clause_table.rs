use std::{cmp::Ordering, collections::HashMap, ops::Deref, usize};

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

        for (ci, (_, clause)) in self.iter(&[ClauseType::CLAUSE, ClauseType::BODY]) {
            let cell = heap.str_symbol_arity(clause[0]);
            if cell.0 >= isize::MAX as usize {
                match predicate_map.get_mut(&cell) {
                    Some(clauses) => clauses.push(ci),
                    None => {
                        predicate_map.insert(cell, vec![ci]);
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
    pub fn iter(&self, c_types: &[ClauseType]) -> ClauseIterator {
        let mut types = [false; 4];
        if c_types.contains(&ClauseType::CLAUSE) {
            types[0] = true;
        }
        if c_types.contains(&ClauseType::BODY) {
            types[1] = true;
        }
        if c_types.contains(&ClauseType::META) {
            types[2] = true;
        }
        if c_types.contains(&ClauseType::HYPOTHESIS) {
            types[3] = true;
        }
        ClauseIterator::new(self, types)
    }

    pub fn get(&self, index: usize) -> (ClauseType, &Clause) {
        // if index >= self.clauses.len(){ return None;}
        let (ctype, literals_ptr, clause_literals_len) = self.clauses[index];
        let clause = &self.literal_addrs[literals_ptr..literals_ptr + clause_literals_len];
        (ctype, clause)
    }
}

impl Deref for ClauseTable {
    type Target = [usize];
    fn deref(&self) -> &[usize] {
        &self.literal_addrs
    }
}

pub struct ClauseIterator<'a> {
    clause_table: &'a ClauseTable,
    i: usize,
    skip_points: Vec<(usize, usize)>, // (start_idx, end_idx) pairs to skip
}

impl<'a> ClauseIterator<'a> {
    fn new(clause_table: &ClauseTable, types: [bool; 4]) -> ClauseIterator {
        let mut skip_points: Vec<(usize, usize)> = Vec::with_capacity(4);

        if !types[3] {
            skip_points.push((clause_table.type_flags[3], clause_table.clauses.len()))
        }

        for type_i in (0..3).rev() {
            if !types[type_i] {
                skip_points.push((
                    clause_table.type_flags[type_i],
                    clause_table.type_flags[type_i + 1],
                ));
            }
        }

        //TO DO Merge skip points if possible

        ClauseIterator {
            clause_table,
            i: 0,
            skip_points,
        }
    }
    fn skip_if_required(&mut self) {
        loop {
            if let Some((start_i, end_i)) = self.skip_points.last().copied() {
                if self.i == start_i {
                    self.i = end_i;
                    self.skip_points.pop();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = (usize, (ClauseType, &'a Clause));

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_if_required();

        if self.i == self.clause_table.clauses.len() {
            return None;
        }
        let result = Some((self.i, self.clause_table.get(self.i)));
        self.i += 1;
        result
    }
}
