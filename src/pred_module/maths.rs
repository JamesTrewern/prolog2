use std::mem;
use crate::{heap::heap::Tag, interface::state::State};

use super::PredModule;
use fsize::fsize;

fn math_equal(call: usize, state: &mut State) -> bool{
    match (state.heap[call+2], state.heap[call+3]){
        ((Tag::INT, bits1), (Tag::INT, bits2)) => bits1==bits2,
        ((Tag::FLT, bits1), (Tag::FLT, bits2)) => unsafe { mem::transmute::<usize, fsize>(bits1)  == mem::transmute::<usize, fsize>(bits2)},
        _ => false
    }

}

pub static MATH: PredModule = &[
    ("=:=",2,math_equal)
];
