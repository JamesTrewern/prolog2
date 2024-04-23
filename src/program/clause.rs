use std::{
    alloc::{self, Layout},
    cmp::Ordering,
    collections::HashMap,
    iter::Map,
    ops::{Deref, Index},
    ptr,
    rc::Rc,
    thread, time,
};

use crate::{
    heap::Heap,
    unification::{unify, unify_rec},
};

pub type Clause<'a> = &'a [usize];

pub type ClauseOwned = Box<[usize]>;

// pub struct Clause {
//     ptr: *mut usize,
//     len: usize,
// }

// impl Deref for Clause {
//     type Target = [usize];
//     fn deref(&self) -> &[usize] {
//         unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
//     }
// }

// impl Clause {

// }

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum ClauseType {
    CONSTRAINT,
    CLAUSE,
    BODY,
    META,
    HYPOTHESIS,
}

fn order_clauses(c1: &(ClauseType, usize, usize), c2: &(ClauseType, usize, usize)) -> Ordering {
    let o1 = match c1.0 {
        ClauseType::CONSTRAINT => 0,
        ClauseType::CLAUSE => 1,
        ClauseType::BODY => 2,
        ClauseType::META => 3,
        ClauseType::HYPOTHESIS => 4,
    };
    let o2 = match c2.0 {
        ClauseType::CONSTRAINT => 0,
        ClauseType::CLAUSE => 1,
        ClauseType::BODY => 2,
        ClauseType::META => 3,
        ClauseType::HYPOTHESIS => 4,
    };
    o1.cmp(&o2)
}

pub trait ClauseTraits {
    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool;
    fn pred_symbol(&self, heap: &Heap) -> usize;
    fn higher_order(&self, heap: &Heap) -> bool;
    fn write_clause(&self, heap: &Heap);
    fn to_string(&self, heap: &Heap) -> String;
}

impl<'a> ClauseTraits for Clause<'a> {
    fn higher_order(&self, heap: &Heap) -> bool {
        self.iter().any(|literal| ho_term(*literal, heap))
    }

    fn write_clause(&self, heap: &Heap) {
        if self.len() == 1 {
            let clause_str = heap.term_string(self[0]);
            println!("{clause_str}.")
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
            println!("{buffer}.");
        }
    }

    fn to_string(&self, heap: &Heap) -> String {
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

    fn pred_symbol(&self, heap: &Heap) -> usize {
        heap[self[0]].0
    }

    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool {
        //TO DO
        //Implement proper Subsumtption
        if self.len() == other.len() {
            let mut binding = match unify(self[0], other[0], heap) {
                Some(b) => b,
                None => return false,
            };
            for i in 1..self.len() {
                if !unify_rec(self[i], other[i], heap, &mut binding) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl ClauseTraits for ClauseOwned {
    fn higher_order(&self, heap: &Heap) -> bool {
        self.iter().any(|literal| ho_term(*literal, heap))
    }

    fn write_clause(&self, heap: &Heap) {
        if self.len() == 1 {
            let clause_str = heap.term_string(self[0]);
            println!("{clause_str}.")
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
            println!("{buffer}.");
        }
    }

    fn to_string(&self, heap: &Heap) -> String {
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

    fn pred_symbol(&self, heap: &Heap) -> usize {
        heap[self[0]].0
    }

    fn subsumes(&self, other: &Clause, heap: &Heap) -> bool {
        //TO DO
        //Implement proper Subsumtption
        if self.len() == other.len() {
            let mut binding = match unify(self[0], other[0], heap) {
                Some(b) => b,
                None => return false,
            };
            for i in 1..self.len() {
                if !unify_rec(self[i], other[i], heap, &mut binding) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

fn ho_struct(addr: usize, heap: &Heap) -> bool {
    let (p, n) = heap[addr];
    if p < Heap::CON_PTR {
        return true;
    }
    for i in 1..n + 1 {
        match heap[addr + i] {
            (Heap::REFA, _) => return true,
            (Heap::STR, ptr) => {
                if ho_struct(ptr, heap) {
                    return true;
                }
            }
            _ => (),
        }
    }
    false
}

fn ho_list(addr: usize, heap: &Heap) -> bool {
    if ho_term(addr, heap) {
        return true;
    }
    if ho_term(addr + 1, heap) {
        return true;
    }
    false
}

fn ho_term(addr: usize, heap: &Heap) -> bool {
    match heap[addr] {
        (Heap::REFA, _) => true,
        (Heap::STR, ptr) => ho_struct(ptr, heap),

        (Heap::LIS, ptr) => ptr != Heap::CON && ho_list(ptr, heap),
        (Heap::CON | Heap::INT, _) => false,
        _ => ho_struct(addr, heap),
    }
}
#[derive(Debug)]
pub struct ClauseTable {
    pub clauses: Vec<(ClauseType, usize, usize)>,
    literal_addrs: Vec<usize>,
    type_flags: [usize; 5],
}

impl<'a> ClauseTable {
    const DEFAULT_CAPACITY: usize = 1000;

    pub fn new() -> ClauseTable {
        ClauseTable {
            clauses: vec![],
            literal_addrs: Vec::with_capacity(Self::DEFAULT_CAPACITY),
            type_flags: [0; 5],
        }
    }

    pub fn add_clause(&mut self, clause: ClauseOwned, clause_type: ClauseType) {
        self.clauses
            .push((clause_type, self.literal_addrs.len(), clause.len()));
        self.literal_addrs.extend_from_slice(&clause);
    }

    pub fn sort_clauses(&mut self) {
        self.clauses.sort_by(|c1, c2| order_clauses(c1, c2));
    }

    pub fn remove_clause(&mut self, i: usize) {
        let (_, literals_ptr, clause_literals_len) = self.clauses.remove(i);
        assert!(
            self.literal_addrs.len() == literals_ptr + clause_literals_len,
            "Clause Not removed from top"
        );
        self.literal_addrs
            .truncate(self.literal_addrs.len() - clause_literals_len)
    }

    pub fn predicate_map(&self, heap: &Heap) -> HashMap<(usize, usize), Vec<usize>> {
        let mut predicate_map = HashMap::<(usize, usize), Vec<usize>>::new();

        for (ci, (_, clause)) in self.iter([false, true, true, false, false]) {
            let cell = heap[clause[0]];
            if cell.0 >= isize::MAX as usize {
                match predicate_map.get_mut(&cell) {
                    Some(clauses) => clauses.push(ci),
                    None => {
                        predicate_map.insert(cell, vec![ci]);
                    }
                }
            }
        }

        predicate_map
    }

    pub fn find_flags(&mut self) {
        self.type_flags = [self.clauses.len(); 5];

        for (i, (ct, _, _)) in self.clauses.iter().enumerate().rev() {
            if *ct == ClauseType::CONSTRAINT {
                self.type_flags[0] = i;
            }
            if *ct == ClauseType::CLAUSE {
                self.type_flags[1] = i;
            }
            if *ct == ClauseType::BODY {
                self.type_flags[2] = i;
            }
            if *ct == ClauseType::META {
                self.type_flags[3] = i;
            }
            if *ct == ClauseType::HYPOTHESIS {
                self.type_flags[4] = i;
            }
        }

        for type_i in (0..4).rev() {
            if self.type_flags[type_i] > self.type_flags[type_i + 1] {
                self.type_flags[type_i] = self.type_flags[type_i + 1]
            }
        }
        println!("{:?}", self.type_flags);
    }

    pub fn iter(&self, types: [bool; 5]) -> ClauseIterator {
        ClauseIterator::new(self, types)
    }

    pub fn get(&self, index: usize) -> (ClauseType, Clause) {
        // if index >= self.clauses.len(){ return None;}
        let (ctype, literals_ptr, clause_literals_len) = self.clauses[index];
        let clause = &self.literal_addrs[literals_ptr .. literals_ptr + clause_literals_len];
        (ctype, clause)
    }
}

impl Deref for ClauseTable {
    type Target = [usize];
    fn deref(&self) -> &[usize] {
        &self.literal_addrs
    }
}
#[derive(Debug)]
pub struct ClauseIterator<'a> {
    clause_table: &'a ClauseTable,
    i: usize,
    skip_points: Vec<(usize, usize)>
}

impl<'a> ClauseIterator<'a> {
    fn new(clause_table: &ClauseTable, types: [bool; 5]) -> ClauseIterator {
        let mut skip_points: Vec<(usize, usize)> = Vec::with_capacity(5);

        if !types[4] {
            skip_points.push((clause_table.type_flags[4], clause_table.clauses.len()))
        }

        for type_i in (0..4).rev() {
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
            skip_points
        }
    }
    fn skip_if_required(&mut self) {
        loop{
            if let Some((i1 ,i2)) =  self.skip_points.last().copied(){
                if self.i == i1{
                    self.i = i2;
                    self.skip_points.pop();
                }else{
                    break;
                }
            }else{
                break;
            }
        }
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = (usize, (ClauseType, Clause<'a>));

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
