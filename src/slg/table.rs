use smallvec::SmallVec;

use crate::heap::{heap::{Cell,Heap, Tag}, query_heap::QueryHeap};

pub struct MetaSub{
    clause_idx: usize, //Index in program clause table to meta-clause
    subs: SmallVec<[usize;6]>, //Array of table heap addresses, Arg Ids of meta vars index array
}

pub struct Possibility{
    over_general: bool,
    bindings: SmallVec<[usize;5]>, //Table heap literal arg ID -> table heap addr
    meta_subs: SmallVec<[MetaSub;3]> //[(Clause Index, Arg bindings -> Table heap addresses)]
}


pub struct Table<'a>{
    heap: QueryHeap<'a>, //Locally stored cells and ref to program heap, allows bindings to be thread independent
    // entries: Vec<Entry> 
}

pub struct TrieNode{
    answers: Option<usize>, //Index of answer set in table
    children: SmallVec<[((Tag,usize),usize);5]> // Cell -> Index of TRIE Node
}

