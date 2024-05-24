use std::mem;

use crate::{heap::Tag, state::Config, Heap, Program};
use super::PredModule;

fn body_pred(call: usize, heap: &mut Heap, _: &mut Config, prog: &mut Program) -> bool{
    let symbol = if let (Tag::CON, symbol) = heap[call+2]{
        symbol
    }else{
        return false;
    };
    let arity: isize = if let (Tag::INT, arity) = &heap[call+3]{
        unsafe { mem::transmute_copy(arity) }
    }else{
        return false;
    };
    prog.add_body_pred(symbol, arity as usize, heap);
    true
}

fn max_h_preds(call: usize, heap: &mut Heap, config: &mut Config, _: &mut Program) -> bool{
    if let (Tag::INT, value) = heap[call+2]{
        config.max_h_pred = value;
        true
    }else{
        false
    }
}

fn max_h_clause(call: usize, heap: &mut Heap, config: &mut Config, _: &mut Program) -> bool{
    if let (Tag::INT, value) = heap[call+2]{
        config.max_h_clause = value;
        true
    }else{
        false
    }
}

fn share_preds(call: usize, heap: &mut Heap, config: &mut Config, _: &mut Program) -> bool{
    let value = match heap[call+2] {
        Heap::TRUE => true,
        Heap::FALSE => false,
        _ => {println!("Value passed to share_preds wasn't true/false"); return false;}
    };
    config.share_preds = value;
    true
}

fn debug(call: usize, heap: &mut Heap, config: &mut Config, _: &mut Program) -> bool{
    let value = match heap[call+2] {
        Heap::TRUE => true,
        Heap::FALSE => false,
        _ => {println!("Value passed to debug wasn't true/false"); return false;}
    };
    config.debug = value;
    true
}

pub static CONFIG: PredModule = &[
    ("body_pred",2,body_pred),
    ("max_h_preds",1,max_h_preds),
    ("max_h_clause",1,max_h_clause),
    ("share_preds",1,share_preds),
    ("debug",1,debug),

];