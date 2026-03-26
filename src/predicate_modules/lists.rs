use std::sync::Arc;

use crate::{
    Config, heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap, symbol_db::SymbolDB,
    }, predicate_modules::PredicateModule, program::{hypothesis::Hypothesis, predicate_table::PredicateTable}
};

use super::{PredReturn,maths::Number};

/// Determine length of list
pub fn length(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    if let (Tag::Lis, mut lis_ptr) = heap[goal + 2] {
        let mut length = 1;
        while let (Tag::Lis, next_ptr) = heap[lis_ptr + 1] {
            length += 1;
            lis_ptr = next_ptr;
        }
        match heap[heap.deref_addr(goal + 3)] {
            (Tag::Ref, addr) => {
                let bind_addr = heap.heap_push((Tag::Int, length));
                PredReturn::Success(vec![(addr, bind_addr)], vec![])
            }
            (Tag::Int, value) => (length == value).into(),
            _ => false.into(),
        }
    } else {
        false.into()
    }
}

/// Sort list by alphabetical or numerical order, second value must be variable
pub fn sort(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let src_addr = if let (Tag::Ref, src_addr) = heap[heap.deref_addr(goal+3)]{
        src_addr
    }else{
        return false.into();
    };
    if let (Tag::Lis, mut lis_ptr) = heap[goal + 2] {
        let mut element_cells = Vec::new();
        loop {
            element_cells.push(heap[lis_ptr]);
            if let (Tag::Lis, next_ptr) = heap[heap.deref_addr(lis_ptr + 1)] {
                lis_ptr = next_ptr;
            } else {
                break;
            }
        }
        //Check all tags are either Con/Stri for alphabetical or Int/Flt for numerical
        let tag = element_cells[0].0;
        match tag {
            Tag::Flt | Tag::Int => {
                if element_cells
                    .iter()
                    .all(|(tag, _)| *tag == Tag::Flt || *tag == Tag::Int)
                {
                    //Created sorted list
                    let mut element_values: Vec<(Cell, Number)> = element_cells
                        .into_iter()
                        .map(|(tag, value)| ((tag, value), Number::from_cell((tag,value))))
                        .collect();
                    element_values.sort_by(|(_,n1),(_,n2)| n1.partial_cmp(n2).unwrap());
                    //
                    let list_addr = heap.heap_push((Tag::Lis,heap.heap_len()+1));
                    for (cell,_) in element_values{
                        heap.heap_push(cell);
                        heap.heap_push((Tag::Lis,heap.heap_len()+1));
                    }
                    *heap.heap_last() = (Tag::ELis,0);
                    PredReturn::Success(vec![(src_addr,list_addr)], vec![])
                } else {
                    false.into()
                }
            }
            Tag::Stri | Tag::Con => {
                if element_cells
                    .iter()
                    .all(|(tag, _)| *tag == Tag::Stri || *tag == Tag::Con)
                {
                    //Created sorted list
                    let mut element_values: Vec<(Cell, Arc<str>)> = element_cells
                        .into_iter()
                        .map(|(tag, value)| ((tag, value), match tag {
                            Tag::Stri => SymbolDB::get_string(value),
                            Tag::Con => SymbolDB::get_const(value),
                            _ => panic!()
                        }))
                        .collect();
                    element_values.sort_by(|(_,str1),(_,str2)| str1.cmp(str2));
                    //
                    let list_addr = heap.heap_push((Tag::Lis,heap.heap_len()+1));
                    for (cell,_) in element_values{
                        heap.heap_push(cell);
                        heap.heap_push((Tag::Lis,heap.heap_len()+1));
                    }
                    *heap.heap_last() = (Tag::ELis,0);
                    PredReturn::Success(vec![(src_addr,list_addr)], vec![])
                } else {
                    false.into()
                }
            },
            _ => false.into(),
        }
    } else {
        false.into()
    }
}

/// Built-in list-predicates
pub static LISTS: PredicateModule = (
    &[("length", 2, length)],
    &[include_str!("../../builtins/lists.pl")],
);
