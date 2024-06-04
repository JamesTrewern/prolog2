use crate::{interface::state::{self, State}, resolution::{solver::Proof, unification::Binding}};

use super::{PredModule, PredReturn};

fn not(call: usize, state: &mut State) -> PredReturn{
    let old_learn = state.config.learn;
    state.config.learn = false;
    let res = match Proof::new(&[call+1], state).next() {
        Some(_) => PredReturn::False,
        None => PredReturn::True,
    };
    state.config.learn = old_learn;
    res
}

pub const META_PREDICATES: PredModule = &[
    ("not", 2, not)
];