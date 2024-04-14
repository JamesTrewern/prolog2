use super::super::heap::heap::Heap;
use super::program::PredModule;

fn equal(args: Box<[usize]>, heap: &mut Heap) -> bool{
    match (heap[args[0]].0,heap[args[1]].0) {
        (Heap::INT, Heap::INT) => heap[args[0]].1 == heap[args[1]].1,
        _ => false
    }
    
}

pub static MATH: PredModule = &[
    ("=:=",2,equal)
];