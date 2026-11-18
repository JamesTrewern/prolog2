//! What each sub hypothesis proves: which positive and which negative
//! examples.
//!
//! [`build_profiles`] proves every example against every sub hypothesis,
//! once, and records the result in an [`HProfile`]. No sub hypothesis is
//! dropped here for entailing a negative, and none is left half profiled.
//! What follows works on the profiles: [`within`] splits them by how many
//! negatives they entail.

use std::{
    fmt::Debug,
    hash::Hash,
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Once,
    },
};

use rayon::prelude::*;

use super::utils::SearchCtx;
use crate::{
    bitflag::BitFlag, heap::QueryHeap, program::MetaSubTrait, resolution::Proof, ResolutionConfig,
};

/// A set of examples, a bit each: those a hypothesis proves.
///
/// The width the pipeline after profiling is written for. An [`HProfile`]
/// can be of any [`BitFlag`].
pub(super) type Coverage = u128;

/// The positives that `profiles` cover between them.
pub(super) fn covered_by<'a, B: BitFlag + 'a>(
    profiles: impl IntoIterator<Item = &'a HProfile<B>>,
) -> B {
    profiles
        .into_iter()
        .fold(B::empty(), |all, p| all.union(&p.coverage))
}

/// What the stages after profiling ask of the set an [`HProfile`] holds.
pub(super) trait ExampleSet: BitFlag + Hash + Ord + Send + Sync + Debug {}

impl<B: BitFlag + Hash + Ord + Send + Sync + Debug> ExampleSet for B {}

/// The examples and the profile of every sub hypothesis, as noise handling
/// passes them around.
#[derive(Clone, Copy)]
pub(super) struct Profiled<'a, B = Coverage> {
    /// The profiles of the sub hypotheses within the negative noise bound.
    pub(super) kept: &'a [HProfile<B>],
    /// The profiles of the others.
    pub(super) rest: &'a [HProfile<B>],
    pub(super) pos_goals: &'a [usize],
    pub(super) neg_goals: &'a [usize],
    pub(super) ctx: SearchCtx<'a>,
}

/// One sub hypothesis and what it proves.
///
/// There is one per sub hypothesis, so it is kept small: `B` is chosen as
/// the narrowest set that holds the examples, and the counts are a byte
/// each. With `u8` sets a profile is 8 bytes, with `u64` 24, with `u128` 48.
#[derive(Clone, Copy, Debug)]
pub(super) struct HProfile<B = Coverage> {
    /// Index of the sub hypothesis in [`SearchCtx::hypotheses`].
    pub(super) h: u32,
    /// Clauses in `h` plus those of every invented predicate it calls; 255
    /// for that many or more.
    pub(super) n_clauses: u8,
    /// Body literals across that same clause set; 255 for that many or more.
    pub(super) n_literals: u8,
    /// The positives it proves.
    pub(super) coverage: B,
    /// The negatives it proves.
    pub(super) neg_coverage: B,
}

/// A count of clauses or of literals, as an [`HProfile`] holds it: 255
/// stands for that many or more.
///
/// The first count to pass 255 is warned of, once for the whole run.
fn small_count(count: usize, what: &str) -> u8 {
    static WARNED: Once = Once::new();
    u8::try_from(count).unwrap_or_else(|_| {
        WARNED.call_once(|| {
            eprintln!(
                "Warning: a sub hypothesis has {count} {what}. Counts above 255 are treated \
                 as 255 when sub hypotheses are compared by size."
            );
        });
        u8::MAX
    })
}

impl<B: BitFlag> HProfile<B> {
    /// Profile sub hypothesis `h`.
    ///
    /// The examples are proved one after another, from the hypothesis's
    /// `MetaSub`s and those of the definitions it depends on.
    fn new(h: u32, pos_goals: &[usize], neg_goals: &[usize], ctx: SearchCtx) -> Self {
        let meta_subs = ctx
            .pdt
            .test_meta_subs(ctx.hypotheses.get(h as usize), ctx.heap);

        let coverage = proved(pos_goals, &meta_subs, ctx);
        let neg_coverage = proved(neg_goals, &meta_subs, ctx);

        let n_literals: usize = meta_subs
            .iter()
            .map(|meta_sub| meta_sub.template(ctx.predicate_table).body().len())
            .sum();
        Self {
            h,
            n_clauses: small_count(meta_subs.len(), "clauses"),
            n_literals: small_count(n_literals, "literals"),
            coverage,
            neg_coverage,
        }
    }
}

/// ResolutionConfig for a test proof: only the debug trace is silenced. `max_depth`
/// is kept to bound recursive candidates.
fn test_config(config: ResolutionConfig) -> ResolutionConfig {
    ResolutionConfig {
        debug: false,
        ..config
    }
}

/// Which of `goals` the ground clauses `meta_subs` prove.
///
/// `goals` are addresses of goals compiled onto the program heap by
/// [`compile_examples`](super::utils::compile_examples).
fn proved<B: BitFlag>(goals: &[usize], meta_subs: &[&[usize]], ctx: SearchCtx) -> B {
    let config = test_config(ctx.config);
    let mut coverage = B::empty();
    for (i, &goal) in goals.iter().enumerate() {
        let mut query_heap = QueryHeap::new(ctx.heap, None);
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], meta_subs);
        if proof.prove(&mut query_heap, ctx.predicate_table, config) {
            coverage.set(i);
        }
    }
    coverage
}

/// Profile every sub hypothesis in [`SearchCtx::hypotheses`]: every example
/// is proved against each, in one pass.
///
/// Hypotheses are profiled in parallel, one rayon task each; the examples
/// *within* a hypothesis run serially, since with thousands of candidates
/// the pool is already saturated at the outer level.
///
/// Nothing is built and nothing is added to the predicate table. The
/// hypotheses and definitions must be ground, their terms on the program
/// heap, and their clause indices good for the predicate table.
///
/// Profiles are returned in hypothesis order.
///
/// # Panics
///
/// If `B` cannot hold as many examples as there are of either kind.
pub(super) fn build_profiles<B: BitFlag + Send>(
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Vec<HProfile<B>> {
    let most = pos_goals.len().max(neg_goals.len());
    assert!(
        most <= B::CAPACITY,
        "{most} examples are more than the {} a coverage of this width holds",
        B::CAPACITY
    );
    let total = u32::try_from(ctx.hypotheses.len()).expect("more than u32::MAX hypotheses");
    let profiled = AtomicUsize::new(0);

    let h_profiles = (0..total)
        .into_par_iter()
        .map(|h| {
            let h_profile = HProfile::new(h, pos_goals, neg_goals, ctx);

            // Throttled: one line per candidate would spend longer painting
            // the terminal than proving the examples.
            let done = profiled.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 256 == 0 || done == total as usize {
                eprint!("\rCoverage: {done}/{total} hypotheses profiled  ");
                let _ = io::stderr().flush();
            }

            h_profile
        })
        .collect();

    eprintln!();
    h_profiles
}

/// Split `profiles` into those entailing at most `neg_noise` negatives and
/// the rest, each still in hypothesis order.
pub(super) fn within<B: BitFlag>(
    profiles: Vec<HProfile<B>>,
    neg_noise: usize,
) -> (Vec<HProfile<B>>, Vec<HProfile<B>>) {
    profiles
        .into_iter()
        .partition(|h_profile| h_profile.neg_coverage.count() <= neg_noise)
}

#[cfg(test)]
pub(super) mod fixture {
    use crate::{
        heap::{Heap, ProgramHeap, Tag::Con, VarReg},
        learners::{
            predicate_unification::PredDefTable, utils::compile_examples, utils::SearchCtx,
        },
        parser::_build_clause,
        program::{MetaSub, PackedMetaSubs, PredicateTable},
        ParallelConfig, ResolutionConfig,
    };

    /// `max_clause` is left at the default: the proofs these tests drive do
    /// not learn, so the hypothesis size limit never comes into it.
    fn config() -> ResolutionConfig {
        ResolutionConfig {
            max_depth: 10,
            debug: false,
            protect_h_preds: false,
            ..ResolutionConfig::default()
        }
    }

    /// A program of background facts and the meta rule `P(X):-Q(X)`, plus
    /// sub hypotheses of its instances.
    pub(in crate::learners) struct Fixture {
        pub(in crate::learners) prog_heap: ProgramHeap,
        pub(in crate::learners) predicate_table: PredicateTable,
        pub(in crate::learners) hypotheses: PackedMetaSubs,
        pub(in crate::learners) pdt: PredDefTable,
        pub(in crate::learners) neg_goals: Vec<usize>,
    }

    /// Sub hypothesis `i` is the clause `head(X):-body(X)` for
    /// `clauses[i] = (head, body)`.
    pub(in crate::learners) fn fixture(clauses: &[(&str, &str)], negatives: &[&str]) -> Fixture {
        let hypotheses: Vec<Vec<(&str, &str)>> = clauses.iter().map(|&c| vec![c]).collect();
        fixture_with_facts(&["bad(c).", "good(d)."], &hypotheses, negatives)
    }

    /// As [`fixture`], over the background `facts` given, and with any
    /// number of clauses to a sub hypothesis.
    pub(in crate::learners) fn fixture_with_facts(
        facts: &[&str],
        clauses: &[Vec<(&str, &str)>],
        negatives: &[&str],
    ) -> Fixture {
        let mut prog_heap = ProgramHeap::new();
        let mut predicate_table = PredicateTable::new();
        for src in ["P(X):-Q(X),{P,Q}."].iter().chain(facts) {
            let clause = _build_clause(&mut prog_heap, src);
            let symbol_arity = prog_heap.symbol_arity(clause.head());
            predicate_table
                .add_clause_to_predicate(clause, symbol_arity)
                .unwrap();
        }
        let rule = predicate_table.get_variable_clauses(1).unwrap();
        let clause_idx = predicate_table.index_of(&rule[0]).unwrap();

        let mut hypotheses = PackedMetaSubs::default();
        for hypothesis in clauses {
            let meta_subs: Vec<MetaSub> = hypothesis
                .iter()
                .map(|(head, body)| {
                    let subs = [head, body].map(|name| {
                        let symbol = prog_heap.symbols().set_const(*name);
                        VarReg::from_addr(prog_heap.heap_push((Con, symbol)))
                    });
                    MetaSub {
                        clause_idx,
                        subs: subs.into_iter().collect(),
                    }
                })
                .collect();
            hypotheses.push(&meta_subs);
        }

        let negatives: Vec<String> = negatives.iter().map(|goal| goal.to_string()).collect();
        let neg_goals = compile_examples(&negatives, &mut prog_heap);
        Fixture {
            prog_heap,
            predicate_table,
            hypotheses,
            pdt: PredDefTable::default(),
            neg_goals,
        }
    }

    impl Fixture {
        pub(in crate::learners) fn ctx(&self, parallel: ParallelConfig) -> SearchCtx<'_> {
            SearchCtx::new(
                &self.prog_heap,
                &self.predicate_table,
                &self.hypotheses,
                &self.pdt,
                config(),
                parallel,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{build_profiles, fixture::fixture, within};
    use crate::bitflag::BitFlag;
    use crate::{learners::utils::compile_examples, ParallelConfig};

    /// Given `good(d)` and `bad(c)`: sub hypothesis 0 proves the positive
    /// `p(d)`, 1 proves the negative `p(c)`, and 2 proves neither.
    const CLAUSES: [(&str, &str); 3] = [("p", "good"), ("p", "bad"), ("q", "good")];

    #[test]
    fn profiles_record_positive_and_negative_coverage() {
        let mut fixture = fixture(&CLAUSES, &["p(c)"]);
        let pos_goals = compile_examples(&["p(d)".to_string()], &mut fixture.prog_heap);
        let ctx = fixture.ctx(ParallelConfig::default());

        // Every one is profiled, then split by the negatives it proves.
        let (kept, rest) = within(build_profiles(&pos_goals, &fixture.neg_goals, ctx), 0);
        let seen = |profiles: &[super::HProfile]| -> Vec<(u32, bool, bool, usize)> {
            profiles
                .iter()
                .map(|p| {
                    (
                        p.h,
                        p.coverage.get(0),
                        p.neg_coverage.get(0),
                        p.coverage.count(),
                    )
                })
                .collect()
        };
        assert_eq!(seen(&kept), vec![(0, true, false, 1), (2, false, false, 0)]);
        assert_eq!(seen(&rest), vec![(1, false, true, 0)]);
        assert!(kept.iter().all(|p| p.n_clauses == 1 && p.n_literals == 1));
    }

    /// The same sub hypotheses profiled with sets of any width prove the
    /// same examples.
    #[test]
    fn profiles_are_the_same_at_every_width() {
        use crate::bitflag::BitFlag;

        fn seen<B: BitFlag + Send>() -> Vec<(u32, Vec<usize>, Vec<usize>, u8, u8)> {
            let mut fixture = fixture(&CLAUSES, &["p(c)"]);
            let pos_goals = compile_examples(&["p(d)".to_string()], &mut fixture.prog_heap);
            let ctx = fixture.ctx(ParallelConfig::default());
            let all: Vec<super::HProfile<B>> = build_profiles(&pos_goals, &fixture.neg_goals, ctx);
            let all: Vec<_> = all
                .iter()
                .map(|p| {
                    let (pos, neg) = (p.coverage.indices(), p.neg_coverage.indices());
                    (p.h, pos, neg, p.n_clauses, p.n_literals)
                })
                .collect();
            // Already in hypothesis order.
            all
        }

        let expected = vec![
            (0, vec![0], vec![], 1, 1),
            (1, vec![], vec![0], 1, 1),
            (2, vec![], vec![], 1, 1),
        ];
        assert_eq!(seen::<u8>(), expected);
        assert_eq!(seen::<u64>(), expected);
        assert_eq!(seen::<u128>(), expected);
        assert_eq!(seen::<[u128; 8]>(), expected);
    }

    #[test]
    fn counts_past_255_are_held_as_255() {
        assert_eq!(super::small_count(0, "clauses"), 0);
        assert_eq!(super::small_count(255, "clauses"), 255);
        assert_eq!(super::small_count(256, "clauses"), 255);
        assert_eq!(super::small_count(100_000, "literals"), 255);
    }

    /// A profile is as small as its sets allow.
    #[test]
    fn a_profile_is_sized_by_its_sets() {
        use super::HProfile;
        use std::mem::size_of;

        assert_eq!(size_of::<HProfile<u8>>(), 8);
        assert_eq!(size_of::<HProfile<u16>>(), 12);
        assert_eq!(size_of::<HProfile<u32>>(), 16);
        assert_eq!(size_of::<HProfile<u64>>(), 24);
        assert_eq!(size_of::<HProfile<u128>>(), 48);
        assert_eq!(size_of::<HProfile<[u128; 2]>>(), 80);
        assert_eq!(size_of::<HProfile<[u128; 4]>>(), 144);
        assert_eq!(size_of::<HProfile<[u128; 8]>>(), 272);
    }

    #[test]
    #[should_panic(expected = "9 examples are more than the 8")]
    fn more_examples_than_the_width_holds_are_refused() {
        let mut fixture = fixture(&CLAUSES, &["p(c)"]);
        let positives: Vec<String> = (0..9).map(|i| format!("p(d{i})")).collect();
        let pos_goals = compile_examples(&positives, &mut fixture.prog_heap);
        let ctx = fixture.ctx(ParallelConfig::default());
        let _: Vec<super::HProfile<u8>> = build_profiles(&pos_goals, &fixture.neg_goals, ctx);
    }
}
