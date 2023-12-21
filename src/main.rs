use std::mem;
use terms::Term;

mod terms;
mod atoms;
mod clause;
mod program;
mod proof;


const MAX_HEAP_SIZE: usize = 1000;

//TO DO only add vars to heap if choice is chosen

fn main() {
    let mut heap: Vec<Term> = Vec::with_capacity(MAX_HEAP_SIZE);
    let test_str = "gay,gays";
    let mut bs: Vec<Box<str>> = vec![];
    for s in test_str.split(','){
        bs.push(s.into());
    }
    println!("{}",bs[0]==bs[1]);
}
