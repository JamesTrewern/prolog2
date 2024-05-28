use crate::{state::Config, Heap, Program};
mod maths;
mod config;

pub type PredicateFN = fn(usize, &mut Heap, &mut Config, &mut Program) -> bool;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];
pub use config::CONFIG;
pub use maths::MATH;

pub fn get_module(name: &str) -> Option<PredModule>{
    match name {
        "config" => Some(CONFIG),
        _ => None
    }
}