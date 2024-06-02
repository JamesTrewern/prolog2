use crate::{
    heap::{
        self, heap::{Heap, Tag}, symbol_db::SymbolDB
    },
    interface::state::{self, State},
    resolution::unification::Binding,
};
use std::{mem, ops::{Add, Div, Mul, Sub}};

use super::{PredModule, PredReturn};
use fsize::fsize;

pub type Funct = fn (usize, &Heap) -> Number;
static mut FUNCTIONS: Vec::<(usize, Funct)> = Vec::new();


enum Number {
    Flt(fsize),
    Int(isize),
}

impl Number{
    fn float(&self) -> fsize{
        match self {
            Number::Flt(v) => *v,
            Number::Int(v) => *v as fsize,
        }
    }

    pub fn power(self, rhs: Self) -> Number{
        match (self, rhs) {
            (Number::Int(v1),Number::Int(v2)) if v2 > 0=> Number::Int(v1.pow(v2.try_into().unwrap())),
            (lhs,rhs) => Number::Flt(lhs.float().powf(rhs.float()))
        }
    }

    pub fn abs(self) -> Number{
        match self{
            Number::Flt(value) => Number::Flt(value.abs()),
            Number::Int(value) => Number::Int(value.abs()),
        }
    }

    pub fn round(self) -> Number{
        match self {
            Number::Flt(value) => Number::Int(value.round() as isize),
            Number::Int(value) => Number::Int(value),
        }
    }
}

impl Add for Number {
    type Output = Number;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1),Number::Int(v2)) => Number::Int(v1+v2),
            (lhs,rhs) => Number::Flt(lhs.float()+rhs.float())
        }
    }
}

impl Sub for Number {
    type Output =  Number;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1),Number::Int(v2)) => Number::Int(v1-v2),
            (lhs,rhs) => Number::Flt(lhs.float()-rhs.float())
        }
    }
}

impl Mul for Number{
    type Output = Number;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1),Number::Int(v2)) => Number::Int(v1*v2),
            (lhs,rhs) => Number::Flt(lhs.float()*rhs.float())
        }
    }
}

impl Div for Number{
    type Output = Number;
    
    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Int(v1),Number::Int(v2)) => Number::Int(v1/v2),
            (lhs,rhs) => Number::Flt(lhs.float()/rhs.float())
        }
    }
}

impl PartialOrd for Number{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Number::Int(v1),Number::Int(v2)) => Some(v1.cmp(v2)),
            _ => self.float().partial_cmp(&other.float())
        }
    }
}

impl PartialEq for Number{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Number::Int(v1),Number::Int(v2)) => v1 == v2,
            (lhs,rhs) => lhs.float()==rhs.float()
        }
    }
}

fn add(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr + 2, heap) + evaluate_term(addr + 3, heap)
}

fn sub(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr + 2, heap) - evaluate_term(addr + 3, heap)
}

fn mul(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr + 2, heap) * evaluate_term(addr + 3, heap)
}

fn div(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr + 2, heap) / evaluate_term(addr + 3, heap)
}

fn pow(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr + 2, heap).power(evaluate_term(addr + 3, heap))
}

fn cos(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().cos())
}

fn sin(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().sin())
}

fn tan(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().tan())
}

fn acos(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().acos())
}

fn asin(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().asin())
}

fn atan(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().atan())
}

fn log(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr + 2, heap).float().log(evaluate_term(addr + 3, heap).float()))
}

fn abs(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr+2, heap).abs()
}

fn round(addr: usize, heap: &Heap) -> Number{
    evaluate_term(addr+2, heap).round()
}

fn to_radians(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr+2, heap).float().to_radians())
}

fn to_degrees(addr: usize, heap: &Heap) -> Number{
    Number::Flt(evaluate_term(addr+2, heap).float().to_degrees())
}

fn evaluate_str(addr: usize, heap: &Heap) -> Number{
    for (id, funct) in unsafe { FUNCTIONS.iter() }{
        if *id == heap[addr+1].1{
            return funct(addr, heap);
        }
    }
    panic!("Unkown function {}", heap.term_string(addr));
}

fn evaluate_term(mut addr: usize, heap: &Heap) -> Number {
    addr = heap.deref_addr(addr);
    match heap[addr] {
        (Tag::STR, _) => evaluate_str(addr, heap),
        (Tag::StrRef, addr) => evaluate_str(addr, heap),
        (Tag::INT, value) => Number::Int(unsafe { mem::transmute(value) }),
        (Tag::FLT, value) => Number::Flt(unsafe { mem::transmute(value) }),
        _ => panic!(
            "{:?} : {} not a valid mathematical expression",
            heap[addr],
            heap.term_string(addr),

        ),
    }
}

fn math_equal(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs == rhs)
}

fn math_not_equal(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs != rhs)
}

fn greater_than(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs > rhs)
}

fn greater_than_or_equal(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs >= rhs)
}

fn less_than(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs < rhs)
}

fn less_than_or_equal(call: usize, state: &mut State) -> PredReturn {
    let lhs = evaluate_term(call + 2, &state.heap);
    let rhs = evaluate_term(call + 3, &state.heap);
    PredReturn::bool(lhs <= rhs)
}

fn is(call: usize, state: &mut State) -> PredReturn {
    println!("{call}");
    let rhs = evaluate_term(call + 3, &state.heap);
    let lhs_addr = state.heap.deref_addr(call + 2);
    if let (Tag::REF, _) = state.heap[lhs_addr] {
        match rhs {
            Number::Flt(value) => {
                state
                    .heap
                    .push((Tag::FLT, unsafe { mem::transmute(value) }));
                PredReturn::Binding(Binding(vec![(lhs_addr, state.heap.len() - 1)]))
            }
            Number::Int(value) => {
                state
                    .heap
                    .push((Tag::INT, unsafe { mem::transmute(value) }));
                PredReturn::Binding(Binding(vec![(lhs_addr, state.heap.len() - 1)]))
            },
        }
    } else {
        let lhs = evaluate_term(lhs_addr, &state.heap);
        PredReturn::bool(lhs == rhs)
    }
}

pub static MATHS: PredModule = &[
    ("=:=", 2, math_equal),
    ("=/=", 2, math_not_equal),
    (">", 2, greater_than),
    (">=", 2, greater_than_or_equal),
    ("<", 2, less_than),
    ("<=", 2, less_than_or_equal),
    ("is", 2, is),
];

static FUNCTION_SYMBOLS: &[(&'static str,Funct)] = &[
    ("+", add),
    ("-", sub),
    ("*", mul),
    ("/", div),
    ("**", pow),    
    ("cos", cos),
    ("sin", sin),
    ("tan", tan),
    ("acos", acos),
    ("asin", asin),
    ("atan", atan),
    ("log", log),
    ("abs", abs),
    ("round", round),
    ("to_degrees", to_degrees),
    ("to_radians", to_radians)
];

pub fn setup_module(state: &mut State){
    unsafe { FUNCTIONS = FUNCTION_SYMBOLS.iter().map(|(symbol, function)| (state.heap.symbols.set_const(symbol), *function)).collect() };
}