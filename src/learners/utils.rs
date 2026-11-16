use std::{
    io::{self, Write},
    ops::{Deref, DerefMut},
};

use crate::{
    heap::{ProgramHeap, QueryHeap},
    parser::{build_clause, tokenise, TokenStream},
    program::PredicateTable,
    resolution::Proof,
    Config,
};

#[derive(Clone, Copy)]
pub(super) struct Coverage(pub u128);

impl Deref for Coverage {
    type Target = u128;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for Coverage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Coverage {
    pub(super) fn from_len(len: usize) -> Self {
        if len > 128 {
            todo!("More than 128 pos examples not yet implemented");
        }
        let mask = u128::MAX << len;
        Self(mask)
    }

    pub(super) fn sub_set(&self, other: &Self) -> bool {
        other.0 | self.0 == other.0
    }

    /// How many bits set in self not set in other
    pub(super) fn difference(&self, other: &Self) -> usize {
        (self.0 & !other.0).count_ones() as usize
    }

    pub(super) fn count(&self, max_bit: usize) -> usize {
        (self.0 & !(u128::MAX << max_bit)).count_ones() as usize
    }

    pub(super) fn set(&mut self, i: usize) {
        self.0 |= 1 << i
    }

    pub(super) fn get(&self, i: usize) -> bool {
        self.0 & 1 << i != 0
    }

    pub(super) fn all(&self) -> bool {
        self.0 == u128::MAX
    }

    pub(super) fn _none(&self) -> bool {
        self.0 == 0
    }
}

/// Compile every example onto the program heap once, returning each one's
/// goal address.
///
/// Learning proves the examples over and over -- every negative against every
/// hypothesis during specialisation, every positive again for coverage and
/// again for reduction -- and each proof used to re-tokenise and rebuild the
/// goal on its own query heap. The terms are identical every time, so they
/// are built once here instead and the proofs are handed addresses.
///
/// This works because a ground goal needs nothing per-proof. A `Ref` cell
/// holds a variable id rather than a heap address, so the only per-proof
/// state a term needs is its variable registers, and a ground goal has none.
/// An example containing a variable would need a register per proof and so
/// cannot be shared this way.
pub(super) fn compile_examples(examples: &[String], heap: &mut ProgramHeap) -> Vec<usize> {
    examples
        .iter()
        .map(|example| {
            let literals = match TokenStream::new(
                tokenise(example).unwrap_or_else(|e| panic!("Example '{example}': {e}")),
            )
            .parse_goals()
            {
                Ok(literals) => literals,
                Err(e) => panic!("Example '{example}' incorrectly formatted: {e}"),
            };

            let mut vars = Vec::new();
            for literal in &literals {
                literal.extract_vars(&mut vars);
            }
            if !vars.is_empty() {
                todo!(
                    "example '{example}' contains the variable(s) {vars:?}; only ground \
                     examples can be compiled onto the shared program heap, because a \
                     variable needs a register per proof"
                );
            }

            build_clause(literals, None, heap, false)[0]
        })
        .collect()
}
/// Count how many positive examples a set of ground clauses, as packed
/// `MetaSub`s, can prove.
pub(super) fn count_coverage(
    pos_goals: &[usize],
    meta_subs: &[&[usize]],
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    max_depth: usize,
) -> (Coverage, usize) {
    // `protect_h_preds` is false because these clauses are ground -- their
    // invented predicates were given constants before they got here, so
    // there is nothing left to protect.
    let config = Config {
        max_depth,
        debug: false,
        protect_h_preds: false,
        ..Config::default()
    };

    let mut coverage = Coverage::from_len(pos_goals.len());

    for (i, &goal) in pos_goals.iter().enumerate() {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], meta_subs);
        if proof.prove(&mut query_heap, predicate_table, config) {
            coverage.set(i);
        }
    }
    let count = coverage.count(pos_goals.len());
    (coverage, count)
}

/// Plotkin's program reduction (Algorithm 3).
/// Sequentially tries removing each clause; if all positives are still provable
/// without it, the clause is redundant and permanently removed.
pub(super) fn reduce<'m>(
    pos_goals: &[usize],
    mut hypothesis: Vec<&'m [usize]>,
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    config: Config,
    verbose: bool,
) -> Vec<&'m [usize]> {
    // Learning is off on the proofs below, not here.
    let config = Config {
        debug: false,
        ..config
    };

    // New reduction method
    // pop clause
    // check coverage if same continue
    // if less coverage add clause to front (design vec with easy front adding)
    // loop until clauses_considered == initial size

    let total = hypothesis.len();
    let mut removed = 0usize;
    let mut i = 0;
    while i < hypothesis.len() {
        if verbose {
            eprint!(
                "\rReduce: {}/{total} checked, {removed} removed    ",
                i + removed + 1
            );
            let _ = io::stderr().flush();
        }

        let c = hypothesis.remove(i);

        // Check if all positive examples are still provable without clause i
        let redundant = pos_goals.iter().all(|&goal| {
            let mut query_heap = QueryHeap::new(heap, None);
            let mut proof = Proof::with_hypothesis(&query_heap, &[goal], hypothesis.as_slice());
            proof.prove(&mut query_heap, predicate_table, config)
        });

        if redundant {
            removed += 1;
            // Don't increment i — next clause slides into this position
        } else {
            hypothesis.insert(i, c);
            i += 1;
        }
    }
    if verbose {
        eprintln!(" ...done");
    }

    hypothesis
}

#[cfg(test)]
mod tests {

    use crate::learners::utils::Coverage;

    #[test]
    fn coverage_sub_set() {
        let mut a = Coverage::from_len(4);
        let mut b = Coverage::from_len(4);

        a.set(0);
        a.set(1);
        b.set(1);
        assert!(!a.sub_set(&b));
        assert!(b.sub_set(&a));

        b.set(0);
        assert!(a.sub_set(&b));
        assert!(b.sub_set(&a));
    }
}
