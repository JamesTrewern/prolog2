use crate::{program, state::Config, Heap, Program};
use super::PredModule;

fn equal(args: usize, heap: &mut Heap, config: &mut Config, prog: &mut Program) -> bool{
    // match (heap[args[0]].0,heap[args[1]].0) {
    //     (Tag::INT, Tag::INT) => heap[args[0]].1 == heap[args[1]].1,
    //     _ => false
    // }
    false
}

pub static MATH: PredModule = &[
    ("=:=",2,equal)
];
