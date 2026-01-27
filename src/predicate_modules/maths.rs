use std::mem;

use crate::heap::{
    heap::{Cell, Heap, Tag},
    query_heap::QueryHeap,
    symbol_db::SymbolDB,
};
use crate::program::hypothesis::Hypothesis;

use super::PredReturn;

use fsize::fsize;

type MathFn = fn(usize, &QueryHeap) -> Number;
static mut FUNCTIONS: Vec<(usize, MathFn)> = Vec::new();

#[derive(Debug, Clone, Copy)]
enum Number {
    Flt(fsize),
    Int(isize),
}

impl Number {
    fn float(&self) -> fsize {
        match self {
            Number::Flt(v) => *v,
            Number::Int(v) => *v as fsize,
        }
    }

    fn to_cell(&self) -> Cell {
        match self {
            Number::Flt(value) => (Tag::Flt, unsafe { mem::transmute(*value) }),
            Number::Int(value) => (Tag::Int, unsafe { mem::transmute(*value) }),
        }
    }
}

impl std::ops::Add for Number {
    type Output = Number;
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => Number::Int(v1 + v2),
            (lhs, rhs) => Number::Flt(lhs.float() + rhs.float()),
        }
    }
}

impl std::ops::Sub for Number {
    type Output = Number;
    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => Number::Int(v1 - v2),
            (lhs, rhs) => Number::Flt(lhs.float() - rhs.float()),
        }
    }
}

impl std::ops::Mul for Number {
    type Output = Number;
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => Number::Int(v1 * v2),
            (lhs, rhs) => Number::Flt(lhs.float() * rhs.float()),
        }
    }
}

impl std::ops::Div for Number {
    type Output = Number;
    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => Number::Int(v1 / v2),
            (lhs, rhs) => Number::Flt(lhs.float() / rhs.float()),
        }
    }
}

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Number::Int(v1), Number::Int(v2)) => v1 == v2,
            (lhs, rhs) => lhs.float() == rhs.float(),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Number::Int(v1), Number::Int(v2)) => Some(v1.cmp(v2)),
            _ => self.float().partial_cmp(&other.float()),
        }
    }
}

// Math operation functions
fn add(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap) + evaluate_term(addr + 3, heap)
}

fn sub(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap) - evaluate_term(addr + 3, heap)
}

fn mul(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap) * evaluate_term(addr + 3, heap)
}

fn div(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap) / evaluate_term(addr + 3, heap)
}

fn evaluate_str(addr: usize, heap: &QueryHeap) -> Number {
    let symbol = heap[addr + 1].1;
    for (id, funct) in unsafe { FUNCTIONS.iter() } {
        if *id == symbol {
            return funct(addr, heap);
        }
    }
    panic!("Unknown function {}", heap.term_string(addr));
}

fn evaluate_term(addr: usize, heap: &QueryHeap) -> Number {
    let addr = heap.deref_addr(addr);
    match heap[addr] {
        (Tag::Func, _) => evaluate_str(addr, heap),
        (Tag::Str, ptr) => evaluate_str(ptr, heap),
        (Tag::Int, value) => Number::Int(unsafe { mem::transmute(value) }),
        (Tag::Flt, value) => Number::Flt(unsafe { mem::transmute(value) }),
        _ => panic!(
            "{:?} : {} not a valid mathematical expression",
            heap[addr],
            heap.term_string(addr),
        ),
    }
}

/// is/2 predicate: evaluates RHS and unifies with LHS
pub fn is_pred(heap: &mut QueryHeap, _hypothesis: &mut Hypothesis, goal: usize) -> PredReturn {
    // Goal structure: Func(3) | Con("is") | LHS | RHS
    let goal_addr = heap.deref_addr(goal);
    let func_addr = match heap[goal_addr] {
        (Tag::Str, ptr) => ptr,
        (Tag::Func, _) => goal_addr,
        _ => panic!("is/2: expected structure, got {:?}", heap[goal_addr]),
    };
    
    let rhs = evaluate_term(func_addr + 3, heap);
    let lhs_addr = heap.deref_addr(func_addr + 2);
    
    match heap[lhs_addr] {
        (Tag::Ref, _) => {
            // LHS is unbound - create binding
            let result_addr = heap.heap_push(rhs.to_cell());
            PredReturn::Binding(vec![(lhs_addr, result_addr)])
        }
        _ => {
            // LHS is bound - check equality
            let lhs = evaluate_term(lhs_addr, heap);
            PredReturn::bool(lhs == rhs)
        }
    }
}

/// Initialize the math functions lookup table
pub fn setup_maths() {
    unsafe {
        FUNCTIONS = vec![
            (SymbolDB::set_const("+".to_string()), add),
            (SymbolDB::set_const("-".to_string()), sub),
            (SymbolDB::set_const("*".to_string()), mul),
            (SymbolDB::set_const("/".to_string()), div),
        ];
    }
}
