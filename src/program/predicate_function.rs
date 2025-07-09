use crate::resolution::{unification::Substitution,proof::Proof};

pub enum PredReturn {
    True,
    False,
    Binding(Substitution),
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

//Take Proof and pointer to function call term and return true(possibly with binding), or false
pub type PredicateFunction = fn(&mut Proof, usize) -> PredReturn;