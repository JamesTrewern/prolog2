use std::{
    alloc::{self, Layout}, cmp::Ordering, collections::HashMap, iter::Map, ops::{Deref, Index}, ptr, rc::Rc, thread, time
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
    ptr: *mut usize,
    cap: usize,
    pub len: usize,
    type_flags: [usize;5],
}

impl<'a> ClauseTable {
    const DEFAULT_CAPACITY: usize = 1000;

    pub fn new() -> ClauseTable {
        let layout = Layout::array::<usize>(Self::DEFAULT_CAPACITY).unwrap();
        assert!(layout.size() <= isize::MAX as usize, "Allocation too large");
        let ptr = unsafe { alloc::alloc(layout) } as *mut usize;
        ClauseTable {
            clauses: vec![],
            ptr,
            cap: Self::DEFAULT_CAPACITY,
            len: 0,
            type_flags: [0;5]
        }
    }

    fn grow(&mut self) {
        let new_cap = 2 * self.cap;
        let new_layout = Layout::array::<usize>(new_cap).unwrap();
        assert!(
            new_layout.size() <= isize::MAX as usize,
            "Clause Memory Allocation too large"
        );
        let old_layout = Layout::array::<usize>(self.cap).unwrap();
        let old_ptr = self.ptr as *mut u8;
        let new_ptr = unsafe { alloc::realloc(old_ptr, old_layout, new_layout.size()) };
        self.ptr = unsafe { alloc::alloc(new_layout) } as *mut usize;
        self.cap = new_cap;
    }

    pub fn add_clause(&mut self, clause: ClauseOwned, clause_type: ClauseType){
        if self.len + clause.len() >= self.cap {
            self.grow();
        }
        let clause_addr = self.len;
        unsafe { ptr::copy(clause.as_ptr(), self.ptr.add(self.len), clause.len()) }
        self.len += clause.len();
        self.clauses.push((clause_type, clause_addr, clause.len()));
        self.clauses.sort_by(|c1, c2| order_clauses(c1, c2));
    }

    pub fn remove_clause(&mut self, i: usize) {
        let (_, clause_addr, clause_len) = self.clauses.remove(i);
        assert!(
            self.len == clause_addr + clause_len,
            "Clause Not removed from top"
        );
        self.len -= clause_len;
    }

    pub fn predicate_map(&self, heap: &Heap) -> HashMap::<(usize,usize),Vec<usize>>{
        let mut predicate_map = HashMap::<(usize,usize),Vec<usize>>::new();

        for (ci,(_,clause)) in self.iter([false,true,true,false,false]){
            let cell = heap[clause[0]];
            if cell.0 >= isize::MAX as usize{
                match predicate_map.get_mut(&cell){
                    Some(clauses) => clauses.push(ci),
                    None => {predicate_map.insert(cell, vec![ci]);},
                }
                
            }
        }

        predicate_map
    }

    pub fn find_flags(&mut self) {

        self.type_flags = [self.clauses.len();5];

        for (i, (ct, _, _)) in self.clauses.iter().enumerate().rev() {
            if *ct == ClauseType::CONSTRAINT {
                self.type_flags[0] = i;
            }
            if *ct == ClauseType::CLAUSE  {
                self.type_flags[1] = i;
            }
            if *ct == ClauseType::BODY  {
                self.type_flags[2] = i;
            }
            if *ct == ClauseType::META  {
                self.type_flags[3] = i;
            }
            if *ct == ClauseType::HYPOTHESIS  {
                self.type_flags[4] = i;
            }
        }

        for type_i in (0..4).rev(){
            if self.type_flags[type_i] > self.type_flags[type_i+1]{
                self.type_flags[type_i] = self.type_flags[type_i+1]
            }
        }
        println!("{:?}", self.type_flags);
    }

    pub fn iter(&self, types: [bool;5]) -> ClauseIterator {
        ClauseIterator::new(self, types)
    }

    pub fn get(&self, index: usize) -> (ClauseType, Clause) {
        // if index >= self.clauses.len(){ return None;}
        let (ctype, clause_addr, clause_len) = self.clauses[index];
        let clause = unsafe {
            std::slice::from_raw_parts(
                self.ptr.add(clause_addr),
                clause_len,
            )
        };
        (ctype, clause)
    }
}

impl Deref for ClauseTable {
    type Target = [usize];
    fn deref(&self) -> &[usize] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
}
#[derive(Debug)]
pub struct ClauseIterator<'a> {
    clause_table: &'a ClauseTable,
    i: usize,
    current_type_i: usize,
    types: [bool;5]
}

impl<'a> ClauseIterator<'a> {
    fn new(clause_table: &ClauseTable, types: [bool;5]) -> ClauseIterator{
        let mut i = clause_table.clauses.len();
        let mut current_type_i = 0;
        for type_i in 0..5{
            if types[type_i] == true{
                i = clause_table.type_flags[type_i];
                current_type_i = type_i;
                break;   
            }
        }
        ClauseIterator{ clause_table, i, types, current_type_i }
    }
    fn increment_i(&mut self){
        self.i += 1;

        for type_i in (0..5).rev(){
            if self.clause_table.type_flags[type_i] <= self.i{
                self.current_type_i = type_i;
                break;
            }
        }
        loop{
            if self.i >= self.clause_table.type_flags[self.current_type_i]{
                if self.types[self.current_type_i]{
                    break;
                }else if self.current_type_i == 4 {
                    self.i = self.clause_table.clauses.len();
                    break;
                }else{
                    self.current_type_i += 1;
                    self.i = self.clause_table.type_flags[self.current_type_i];
                }
            }else{
                self.current_type_i += 1;
            }
        }
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = (usize,( ClauseType, Clause<'a>));

    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.clause_table.clauses.len(){
            return None;
        }
        println!("{}",self.i);
        let result = Some((self.i, self.clause_table.get(self.i)));
        self.increment_i();
        result
    }
}
