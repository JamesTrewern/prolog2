use smallvec::SmallVec;

use crate::{
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
    },
    slg::answer::MetaSub,
};

pub struct Table<'a> {
    heap: QueryHeap<'a>, //Locally stored cells and ref to program heap, allows bindings to be thread independent
    meta_subs: Vec<MetaSub>, // entries: Vec<Entry>
}

impl<'a> Table<'a> {
    pub fn call(&mut self, call_heap: QueryHeap<'a>, call_goal: usize) {
        let token_stream = Vec::<Cell>::new();
    }
}

fn get_token_stream(heap: &impl Heap, mut term_addr: usize, token_stream: &mut Vec<Cell>, ref_order: &mut Vec<usize>) {
    term_addr = heap.deref_addr(term_addr);
    match heap[term_addr] {
        (Tag::Str, ptr) => get_token_stream(heap, term_addr, token_stream, ref_order),
        (tag @ (Tag::Comp | Tag::Tup | Tag::Set), len) => {
            token_stream.push((tag, len));
            for term_addr in heap.str_iterator(term_addr) {
                get_token_stream(heap, term_addr, token_stream, ref_order);
            }
        }
        (Tag::Ref, addr) => {
            let arg_id = if let Some(idx) = ref_order.iter().position(|el|*el==addr){
                idx
            }else{
                ref_order.push(addr);
                ref_order.len()-1
            };
        }
        cell @ (Tag::Con | Tag::Flt | Tag::Int | Tag::Stri, _) => token_stream.push(cell),
        _ => todo!(),
    }
}
