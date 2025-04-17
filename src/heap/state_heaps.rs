use std::sync::{RwLock, RwLockReadGuard};

use super::{heap::Cell, query_heap::QueryHeap};

pub struct Heaps<'a> {
    program_heap: RwLock<Vec<Cell>>,
    query_heaps: Vec<RwLock<QueryHeap<'a>>>,
}

impl<'a> Heaps<'a> {
    fn new() -> Heaps<'a>{
        Heaps {
            program_heap: RwLock::new(Vec::new()),
            query_heaps: Vec::new()
        }
    }

    fn new_query(&mut self){
        let idx = self.query_heaps.len();
        
    }
}

#[cfg(test)]
mod tests {
    use crate::heap::query_heap::QueryHeap;

    #[test]
    fn test1(){
    }
}