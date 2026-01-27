// use crate::{interface::state::{self, State}, resolution::{solver::Proof, unification::Binding}};

use super::{PredModule, PredReturn};

use crate::{program::dynamic_program::{DynamicProgram, Hypothesis}, resolution::solver::Proof};

fn not(call: usize, proof: &mut Proof) -> PredReturn {
    let mut config = *proof.state.config.read().unwrap();
    config.learn = false;

    let res = match Proof::new(
        &[call + 2],
        proof.store.clone(),
        Hypothesis::Static(&proof.prog.hypothesis),
        Some(config),
        &proof.state,
    )
    .next()
    {
        Some(_) => PredReturn::False,
        None => PredReturn::True,
    };
    res
}

pub const META_PREDICATES: PredModule = &[("not", 1, not)];
