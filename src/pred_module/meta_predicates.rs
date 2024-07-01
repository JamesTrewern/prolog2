// use crate::{interface::state::{self, State}, resolution::{solver::Proof, unification::Binding}};

use super::{PredModule, PredReturn};

use crate::{program::program::DynamicProgram, resolution::solver::Proof};

fn not(call: usize, proof: &mut Proof) -> PredReturn {
    let mut config = *proof.state.config.read().unwrap();
    config.learn = false;

    let prog = DynamicProgram::new(
        Some(proof.prog.hypothesis.clone()),
        proof.state.program.read().unwrap(),
    );

    let res = match Proof::new(
        &[call + 2],
        proof.store.clone(),
        prog,
        Some(config),
        proof.state,
    )
    .next()
    {
        Some(_) => PredReturn::False,
        None => PredReturn::True,
    };
    res
}

pub const META_PREDICATES: PredModule = &[("not", 1, not)];
