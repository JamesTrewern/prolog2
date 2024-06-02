use crate::{interface::state::State, resolution::unification::Binding};
pub mod maths;
pub mod config;

pub enum PredReturn {
    True,
    False,
    Binding(Binding)
}

impl PredReturn{
    pub fn bool(value: bool) -> PredReturn{
        if value{
            PredReturn::True
        }else{
            PredReturn::False
        }
    }
}

pub type PredicateFN = fn(usize, &mut State) -> PredReturn;
pub type PredModule = &'static [(&'static str, usize, PredicateFN)];
pub use config::CONFIG;
pub use maths::MATHS;

fn nothing(_: &mut State){}

pub fn get_module(name: &str) -> Option<(PredModule, fn (&mut State))>{
    match name {
        "config" => Some((CONFIG, nothing)),
        "maths" => {Some((MATHS, maths::setup_module))},
        _ => None
    }
}