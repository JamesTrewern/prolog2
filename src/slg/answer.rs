use smallvec::SmallVec;

pub struct MetaSub{
    meta_clause_idx: usize,
    arg_bindings: [usize; 32]    
}

pub struct Answer{
    // Table key represented with arg bindings. Arg Id -> table heap address
    bindings: SmallVec<[usize;3]>, 
    // Optional Meta-Subs
    meta_subs: Vec<usize> //Index to meta-subs stored in table. For depuplication
}

impl Answer {
    pub fn new() -> Self{
        Answer { bindings: SmallVec::new(), meta_subs: Vec::new() }
    }
}