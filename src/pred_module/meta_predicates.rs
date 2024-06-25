// use crate::{interface::state::{self, State}, resolution::{solver::Proof, unification::Binding}};

use super::{PredModule, PredReturn};

use crate::{interface::config::Config, resolution::solver::Proof};

fn not(call: usize, proof: &mut Proof) -> PredReturn {
    let mut config = Config::get_config();
    config.learn = false;
    let res = match Proof::new(
        &[call + 2],
        proof.store.clone(),
        proof.prog.clone(),
        Some(config),
    )
    .next()
    {
        Some(_) => PredReturn::False,
        None => PredReturn::True,
    };
    res
}

pub const META_PREDICATES: PredModule = &[("not", 1, not)];
