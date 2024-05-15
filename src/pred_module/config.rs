use crate::{state::Config, Heap, Program};
use super::PredModule;

fn body_pred(call: usize, heap: &mut Heap, _: &mut Config, prog: &mut Program) -> bool{
    let symbol = if let (Heap::CON, symbol) = heap[call+2]{
        symbol
    }else{
        return false;
    };
    let arity = if let (Heap::INT, arity) = heap[call+2]{
        arity
    }else{
        return false;
    };

    prog.add_body_pred(symbol, arity, heap);
    true
}

pub static CONFIG: PredModule = &[
    ("body_pred",2,body_pred)
];