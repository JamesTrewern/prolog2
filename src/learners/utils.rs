use super::predicate_unification::PredDefTable;
use crate::{
    heap::{ProgramHeap, QueryHeap},
    parser::{build_clause, tokenise, TokenStream},
    program::{PackedMetaSubs, PredicateTable},
    resolution::Proof,
    ParallelConfig, ResolutionConfig,
};

/// The read-only program context every stage after generalisation needs.
///
/// These travel together through profiling, the noise report and the pool,
/// so they are passed as one value rather than re-listed at each hop.
/// `Copy`, so handing it on costs nothing.
#[derive(Clone, Copy)]
pub(super) struct SearchCtx<'a> {
    pub(super) heap: &'a ProgramHeap,
    pub(super) predicate_table: &'a PredicateTable,
    /// The hypotheses, named by index.
    pub(super) hypotheses: &'a PackedMetaSubs,
    /// The definitions of the predicates they invent.
    pub(super) pdt: &'a PredDefTable,
    pub(super) config: ResolutionConfig,
    pub(super) parallel: ParallelConfig,
}

impl<'a> SearchCtx<'a> {
    pub(super) fn new(
        heap: &'a ProgramHeap,
        predicate_table: &'a PredicateTable,
        hypotheses: &'a PackedMetaSubs,
        pdt: &'a PredDefTable,
        config: ResolutionConfig,
        parallel: ParallelConfig,
    ) -> Self {
        Self {
            heap,
            predicate_table,
            hypotheses,
            pdt,
            config,
            parallel,
        }
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
                // An example is the literal alone; the parser wants its `.`.
                tokenise(format!("{example}."))
                    .unwrap_or_else(|e| panic!("Example '{example}': {e}")),
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
/// Plotkin's program reduction (Algorithm 3).
/// Sequentially tries removing each clause; if all positives are still provable
/// without it, the clause is redundant and permanently removed.
pub(super) fn reduce<'m>(
    pos_goals: &[usize],
    mut hypothesis: Vec<&'m [usize]>,
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
    config: ResolutionConfig,
) -> Vec<&'m [usize]> {
    // Learning is off on the proofs below, not here.
    let config = ResolutionConfig {
        debug: false,
        ..config
    };

    let mut i = 0;
    while i < hypothesis.len() {
        let clause = hypothesis.remove(i);

        // Are all the positives still provable without it?
        let redundant = pos_goals.iter().all(|&goal| {
            let mut query_heap = QueryHeap::new(heap, None);
            let mut proof = Proof::with_hypothesis(&query_heap, &[goal], hypothesis.as_slice());
            proof.prove(&mut query_heap, predicate_table, config)
        });

        // A redundant clause stays out, and the next slides into its place.
        if !redundant {
            hypothesis.insert(i, clause);
            i += 1;
        }
    }
    hypothesis
}
