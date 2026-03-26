use super::{PredReturn, PredicateModule};
use crate::{
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::known_symbol_id,
    },
    program::hypothesis::Hypothesis,
    program::predicate_table::PredicateTable,
    Config,
};

use fsize::fsize;

/// Signature for functions in the [`FUNCTIONS`] table.
/// Returns `None` if any sub-expression is not a valid arithmetic term.
type MathFn = fn(usize, &QueryHeap) -> Option<Number>;

// Minus symbol ID for distinguishing unary negation from binary subtraction
const MINUS_SYMBOL: usize = known_symbol_id(3);

// Math functions array using compile-time known symbol IDs
// Indices match KNOWN_SYMBOLS in symbol_db.rs:
// 0: false, 1: true, 2: +, 3: -, 4: *, 5: /, 6: **
// 7: cos, 8: sin, 9: tan, 10: acos, 11: asin, 12: atan
// 13: log, 14: abs, 15: round, 16: sqrt, 17: to_degrees, 18: to_radians
const FUNCTIONS: [(usize, MathFn); 17] = [
    (known_symbol_id(2), add),         // +
    (known_symbol_id(3), sub),         // -
    (known_symbol_id(4), mul),         // *
    (known_symbol_id(5), div),         // /
    (known_symbol_id(6), pow),         // **
    (known_symbol_id(7), cos),         // cos
    (known_symbol_id(8), sin),         // sin
    (known_symbol_id(9), tan),         // tan
    (known_symbol_id(10), acos),       // acos
    (known_symbol_id(11), asin),       // asin
    (known_symbol_id(12), atan),       // atan
    (known_symbol_id(13), log),        // log
    (known_symbol_id(14), abs),        // abs
    (known_symbol_id(15), round),      // round
    (known_symbol_id(16), sqrt),       // sqrt
    (known_symbol_id(17), to_degrees), // to_degrees
    (known_symbol_id(18), to_radians), // to_radians
];

#[derive(Debug, Clone, Copy)]
pub(super) enum Number {
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
            Number::Flt(value) => (Tag::Flt, f64::to_bits(*value) as usize),
            Number::Int(value) => (Tag::Int, isize::cast_unsigned(*value)),
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

    /// Convert a heap cell known to be `Int` or `Flt` into a `Number`.
    ///
    /// # Panics
    ///
    /// This is an internal helper and should only ever be called with a cell
    /// whose tag is `Int` or `Flt`. Calling it with any other tag is a
    /// programmer error and will hit the `unreachable!` branch.
    pub fn from_cell((tag, value): Cell) -> Self {
        match tag {
            Tag::Flt => Self::flt_from_value(value),
            Tag::Int => Number::Int(usize::cast_signed(value)),
            _ => unreachable!("from_cell called with non-numeric tag {:?}", tag),
        }
    }

    pub fn flt_from_value(value: usize) -> Self {
        #[cfg(target_pointer_width = "32")]
        let float_value = fsize::from_bits(value as u32);

        #[cfg(target_pointer_width = "64")]
        let float_value = fsize::from_bits(value as u64);

        Number::Flt(float_value)
    }
}

impl std::ops::Add for Number {
    type Output = Number;
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => match v1.checked_add(v2) {
                Some(result) => Number::Int(result),
                None => Number::Flt(v1 as f64 + v2 as f64),
            },
            (lhs, rhs) => Number::Flt(lhs.float() + rhs.float()),
        }
    }
}

impl std::ops::Sub for Number {
    type Output = Number;
    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => match v1.checked_sub(v2) {
                Some(result) => Number::Int(result),
                None => Number::Flt(v1 as f64 - v2 as f64),
            },
            (lhs, rhs) => Number::Flt(lhs.float() - rhs.float()),
        }
    }
}

impl std::ops::Mul for Number {
    type Output = Number;
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => match v1.checked_mul(v2) {
                Some(result) => Number::Int(result),
                None => Number::Flt(v1 as f64 * v2 as f64),
            },
            (lhs, rhs) => Number::Flt(lhs.float() * rhs.float()),
        }
    }
}

impl std::ops::Div for Number {
    type Output = Number;
    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1), Number::Int(v2)) => {
                if v2 == 0 {
                    Number::Flt(f64::NAN)
                } else {
                    Number::Int(v1 / v2)
                }
            }
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

// ---------------------------------------------------------------------------
// Math operation functions — all return Option<Number> so that a bad
// sub-expression propagates as None rather than panicking.
// ---------------------------------------------------------------------------

fn add(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)? + evaluate_term(addr + 3, heap)?)
}

fn sub(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)? - evaluate_term(addr + 3, heap)?)
}

fn mul(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)? * evaluate_term(addr + 3, heap)?)
}

fn div(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)? / evaluate_term(addr + 3, heap)?)
}

fn pow(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)?.power(evaluate_term(addr + 3, heap)?))
}

fn cos(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().cos()))
}

fn sin(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().sin()))
}

fn tan(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().tan()))
}

fn acos(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().acos()))
}

fn asin(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().asin()))
}

fn atan(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().atan()))
}

fn log(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(
        evaluate_term(addr + 2, heap)?
            .float()
            .log(evaluate_term(addr + 3, heap)?.float()),
    ))
}

fn abs(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)?.abs())
}

fn round(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(evaluate_term(addr + 2, heap)?.round())
}

fn to_radians(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().to_radians()))
}

fn to_degrees(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().to_degrees()))
}

fn neg(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(match evaluate_term(addr + 2, heap)? {
        Number::Int(v) => Number::Int(-v),
        Number::Flt(v) => Number::Flt(-v),
    })
}

fn sqrt(addr: usize, heap: &QueryHeap) -> Option<Number> {
    Some(Number::Flt(evaluate_term(addr + 2, heap)?.float().sqrt()))
}

/// Evaluate a functor/structure term as an arithmetic expression.
/// Returns `None` if the functor is not a known arithmetic operator.
fn evaluate_str(addr: usize, heap: &QueryHeap) -> Option<Number> {
    let symbol = heap[addr + 1].1;
    let arity = heap[addr].1;

    // Unary minus: -(X) has arity 2 (functor cell + 1 arg)
    if symbol == MINUS_SYMBOL && arity == 2 {
        return neg(addr, heap);
    }

    for (id, funct) in FUNCTIONS.iter() {
        if *id == symbol {
            return funct(addr, heap);
        }
    }
    None
}

/// Evaluate a heap term as an arithmetic expression.
/// Returns `None` if the term is not a number or a known arithmetic expression.
fn evaluate_term(addr: usize, heap: &QueryHeap) -> Option<Number> {
    let addr = heap.deref_addr(addr);
    match heap[addr] {
        (Tag::Func, _) => evaluate_str(addr, heap),
        (Tag::Str, ptr) => evaluate_str(ptr, heap),
        (tag @ (Tag::Int | Tag::Flt), value) => Some(Number::from_cell((tag, value))),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Shared helper for comparison predicates
// ---------------------------------------------------------------------------

/// Resolve the goal to its functor address and evaluate both arguments as numbers.
/// Returns `None` if the goal is malformed or either argument is not a valid
/// arithmetic expression — the caller should treat this as failure.
fn eval_comparison(heap: &QueryHeap, goal: usize) -> Option<(Number, Number)> {
    let goal_addr = heap.deref_addr(goal);
    let func_addr = match heap[goal_addr] {
        (Tag::Str, ptr) => ptr,
        (Tag::Func, _) => goal_addr,
        _ => return None,
    };
    Some((
        evaluate_term(func_addr + 2, heap)?,
        evaluate_term(func_addr + 3, heap)?,
    ))
}

// ---------------------------------------------------------------------------
// Predicate functions
// ---------------------------------------------------------------------------

/// `is/2`: evaluate the RHS as an arithmetic expression and unify with the LHS.
///
/// - If LHS is an unbound variable, it is bound to the result.
/// - If LHS is already bound, the predicate succeeds only if LHS equals the result.
/// - Fails (rather than panicking) if either side is not a valid arithmetic expression.
pub fn is_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _pred_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let goal_addr = heap.deref_addr(goal);
    let func_addr = match heap[goal_addr] {
        (Tag::Str, ptr) => ptr,
        (Tag::Func, _) => goal_addr,
        _ => return PredReturn::False,
    };

    let Some(rhs) = evaluate_term(func_addr + 3, heap) else {
        return PredReturn::False;
    };
    let lhs_addr = heap.deref_addr(func_addr + 2);

    match heap[lhs_addr] {
        (Tag::Ref, _) => {
            // LHS is unbound — bind it to the result
            let result_addr = heap.heap_push(rhs.to_cell());
            PredReturn::Success(vec![(lhs_addr, result_addr)], vec![])
        }
        _ => {
            // LHS is already bound — check numeric equality
            match evaluate_term(lhs_addr, heap) {
                Some(lhs) => (lhs == rhs).into(),
                None => PredReturn::False,
            }
        }
    }
}

/// `</2`: succeeds if LHS evaluates to a number strictly less than RHS.
pub fn lt_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    match eval_comparison(heap, goal) {
        Some((lhs, rhs)) => (lhs < rhs).into(),
        None => PredReturn::False,
    }
}

/// `>/2`: succeeds if LHS evaluates to a number strictly greater than RHS.
pub fn gt_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    match eval_comparison(heap, goal) {
        Some((lhs, rhs)) => (lhs > rhs).into(),
        None => PredReturn::False,
    }
}

/// `=</2`: succeeds if LHS evaluates to a number less than or equal to RHS.
pub fn le_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    match eval_comparison(heap, goal) {
        Some((lhs, rhs)) => (lhs <= rhs).into(),
        None => PredReturn::False,
    }
}

/// `>=/2`: succeeds if LHS evaluates to a number greater than or equal to RHS.
pub fn ge_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    match eval_comparison(heap, goal) {
        Some((lhs, rhs)) => (lhs >= rhs).into(),
        None => PredReturn::False,
    }
}

/// `=:=/2`: succeeds if both sides evaluate to numerically equal values.
///
/// Unlike `is/2`, this never binds variables — both sides must already be
/// ground arithmetic expressions.
pub fn arith_eq_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    match eval_comparison(heap, goal) {
        Some((lhs, rhs)) => (lhs == rhs).into(),
        None => PredReturn::False,
    }
}

/// Built-in maths predicates.
pub static MATHS: PredicateModule = (
    &[
        ("is", 2, is_pred),
        ("<", 2, lt_pred),
        (">", 2, gt_pred),
        ("=<", 2, le_pred),
        (">=", 2, ge_pred),
        ("=:=", 2, arith_eq_pred),
    ],
    &[],
);
