use std::{error, mem};
use crate::{heap::{self, heap::{Heap, Tag}}, interface::state::State};

use super::{get_module, PredModule, PredReturn};

fn body_pred(call: usize, state: &mut State) -> PredReturn{
    let symbol = if let (Tag::CON, symbol) = state.heap[call+2]{
        symbol
    }else{
        return PredReturn::False;
    };
    let arity: isize = if let (Tag::INT, arity) = &state.heap[call+3]{
        unsafe { mem::transmute_copy(arity) }
    }else{
        return PredReturn::False;
    };
    state.prog.add_body_pred(symbol, arity as usize, &state.heap);
    PredReturn::True
}

fn max_h_preds(call: usize, state: &mut State) -> PredReturn{
    if let (Tag::INT, value) = state.heap[call+2]{
        state.config.max_h_pred = value;
        PredReturn::True
    }else{
        PredReturn::False
    }
}

fn max_h_clause(call: usize, state: &mut State) -> PredReturn{
    if let (Tag::INT, value) = state.heap[call+2]{
        state.config.max_h_clause = value;
        PredReturn::True
    }else{
        PredReturn::False
    }
}

fn share_preds(call: usize, state: &mut State) -> PredReturn{
    let value = match state.heap[call+2] {
        Heap::TRUE => true,
        Heap::FALSE => false,
        _ => {println!("Value passed to share_preds wasn't true/false"); return PredReturn::False;}
    };
    state.config.share_preds = value;
    PredReturn::True
}

fn debug(call: usize, state: &mut State) -> PredReturn{
    let value = match state.heap[call+2] {
        Heap::TRUE => true,
        Heap::FALSE => false,
        _ => {println!("Value passed to debug wasn't true/false"); return PredReturn::False;}
    };
    state.config.debug = value;
    PredReturn::True
}

pub fn load_module(call: usize, state: &mut State) -> PredReturn {
    let name = match state.heap[call+2] {
        (Tag::CON, id) => state.heap.term_string(call+2),
        _ => return PredReturn::False
    };
    state.load_module(&name);
    PredReturn::True
}

pub fn load_file(call: usize, state: &mut State) -> PredReturn{
    if let (Tag::LIS, addr) = state.heap[call]{
        let file_path = state.heap.symbols.get_symbol(state.heap[addr].1);
        println!("load: {file_path}");
        match  state.load_file(&file_path){
            Ok(_) => PredReturn::True,
            Err(error) => {println!("{error}"); PredReturn::False},
        }
    }else{
        let file_path = state.heap.symbols.get_symbol(state.heap[call+2].1);
        match  state.load_file(&file_path){
            Ok(_) => PredReturn::True,
            Err(error) => {println!("{error}"); PredReturn::False},
        }
    }
}

pub static CONFIG: PredModule = &[
    ("body_pred",2,body_pred),
    ("max_h_preds",1,max_h_preds),
    ("max_h_clause",1,max_h_clause),
    ("share_preds",1,share_preds),
    ("debug",1,debug),
    ("load_module",1,load_module),
    ("load_file",1,load_file),
];