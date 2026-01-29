use std::sync::Arc;

use super::PredReturn;
use crate::{Config, heap::{
    heap::{Cell, Heap, Tag},
    query_heap::QueryHeap,
    symbol_db::known_symbol_id,
}, program::predicate_table::PredicateTable};
use crate::program::hypothesis::Hypothesis;

use fsize::fsize;

type MathFn = fn(usize, &QueryHeap) -> Number;

// Minus symbol ID for distinguishing unary negation from binary subtraction
const MINUS_SYMBOL: usize = known_symbol_id(3);

// Math functions array using compile-time known symbol IDs
// Indices match KNOWN_SYMBOLS in symbol_db.rs:
// 0: false, 1: true, 2: +, 3: -, 4: *, 5: /, 6: **
// 7: cos, 8: sin, 9: tan, 10: acos, 11: asin, 12: atan
// 13: log, 14: abs, 15: round, 16: sqrt, 17: to_degrees, 18: to_radians
const FUNCTIONS: [(usize, MathFn); 17] = [
    (known_symbol_id(2), add),    // +
    (known_symbol_id(3), sub),    // -
    (known_symbol_id(4), mul),    // *
    (known_symbol_id(5), div),    // /
    (known_symbol_id(6), pow),    // **
    (known_symbol_id(7), cos),    // cos
    (known_symbol_id(8), sin),    // sin
    (known_symbol_id(9), tan),    // tan
    (known_symbol_id(10), acos),  // acos
    (known_symbol_id(11), asin),  // asin
    (known_symbol_id(12), atan),  // atan
    (known_symbol_id(13), log),   // log
    (known_symbol_id(14), abs),   // abs
    (known_symbol_id(15), round), // round
    (known_symbol_id(16), sqrt),  // sqrt
    (known_symbol_id(17), to_degrees),  // to_degrees
    (known_symbol_id(18), to_radians),  // to_radians
];

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
            Number::Flt(value) => (Tag::Flt, f64::to_bits(*value) as usize ),
            Number::Int(value) => (Tag::Int, isize::cast_unsigned(*value) ),
        }
    }

    pub fn power(self, rhs: Self) -> Number {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) if v2 > 0 => {
                Number::Int(v1.pow(v2.try_into().unwrap()))
            }
            (lhs, rhs) => Number::Flt(lhs.float().powf(rhs.float())),
        }
    }

    pub fn abs(self) -> Number {
        match self {
            Number::Flt(value) => Number::Flt(value.abs()),
            Number::Int(value) => Number::Int(value.abs()),
        }
    }

    pub fn round(self) -> Number {
        match self {
            Number::Flt(value) => Number::Int(value.round() as isize),
            Number::Int(value) => Number::Int(value),
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

fn pow(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap).power(evaluate_term(addr + 3, heap))
}

fn cos(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().cos())
}

fn sin(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().sin())
}

fn tan(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().tan())
}

fn acos(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().acos())
}

fn asin(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().asin())
}

fn atan(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().atan())
}

fn log(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(
        evaluate_term(addr + 2, heap)
            .float()
            .log(evaluate_term(addr + 3, heap).float()),
    )
}

fn abs(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap).abs()
}

fn round(addr: usize, heap: &QueryHeap) -> Number {
    evaluate_term(addr + 2, heap).round()
}

fn to_radians(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().to_radians())
}

fn to_degrees(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().to_degrees())
}

fn neg(addr: usize, heap: &QueryHeap) -> Number {
    match evaluate_term(addr + 2, heap) {
        Number::Int(v) => Number::Int(-v),
        Number::Flt(v) => Number::Flt(-v),
    }
}

fn sqrt(addr: usize, heap: &QueryHeap) -> Number {
    Number::Flt(evaluate_term(addr + 2, heap).float().sqrt())
}

fn evaluate_str(addr: usize, heap: &QueryHeap) -> Number {
    let symbol = heap[addr + 1].1;
    let arity = heap[addr].1;
    
    // Handle unary minus: -(X) has arity 2 (functor + 1 arg)
    if symbol == MINUS_SYMBOL && arity == 2 {
        return neg(addr, heap);
    }
    
    for (id, funct) in FUNCTIONS.iter() {
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
        (Tag::Int, value) => Number::Int(usize::cast_signed(value)),
        (Tag::Flt, value) => {
            #[cfg(target_pointer_width = "32")]
            let float_value = fsize::from_bits(value as u32);

            #[cfg(target_pointer_width = "64")]
            let float_value = fsize::from_bits(value as u64);

            Number::Flt(float_value)
        },
        _ => panic!(
            "{:?} : {} not a valid mathematical expression",
            heap[addr],
            heap.term_string(addr),
        ),
    }
}

/// is/2 predicate: evaluates RHS and unifies with LHS
pub fn is_pred(heap: &mut QueryHeap, _hypothesis: &mut Hypothesis, goal: usize, _pred_table: Arc<PredicateTable>, _config: Config) -> PredReturn {
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
