use crate::resolution::{solver::Proof, unification::Binding};
pub mod config_mod;
pub mod maths;
pub mod meta_predicates;
pub mod top_prog;

pub enum PredReturn {
    True,
    False,
    Binding(Binding),
}

impl PredReturn {
    pub fn bool(value: bool) -> PredReturn {
        if value {
            PredReturn::True
        } else {
            PredReturn::False
        }
    }
}

pub type PredicateFN = fn(usize, &mut Proof) -> PredReturn;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];
pub use config_mod::CONFIG_MOD;
pub use maths::MATHS;
use meta_predicates::META_PREDICATES;
use top_prog::TOP_PROGRAM;

fn nothing() {}

pub fn get_module(name: &str) -> Option<(PredModule, fn())> {
    match name {
        "config" => Some((CONFIG_MOD, nothing)),
        "maths" => Some((MATHS, maths::setup_module)),
        "meta_preds" => {Some((META_PREDICATES, nothing))},
        "top_prog" => {Some((TOP_PROGRAM, nothing))},
        _ => None,
    }
}

#[cfg(test)]
mod tests;
