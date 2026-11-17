//! What each sub hypothesis proves: which positive and which negative
//! examples.
//!
//! [`build_profiles`] replaces specialisation as a pass of its own. A sub
//! hypothesis is no longer simply kept or dropped for entailing a negative:
//! its coverage of both example sets is recorded in an [`HProfile`].
//! [`build_profiles`] keeps those entailing no negative, and
//! [`profile_rest`] profiles the others once [noise handling](super::noise)
//! finds it needs them.

use std::{
    io::{self, Write},
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering},
};

use rayon::prelude::*;

use super::sub_h_comb::SearchCtx;
use crate::{heap::QueryHeap, program::MetaSubTrait, resolution::Proof, ResolutionConfig};

/// A bit per example, set when it is proved. Bits past the number of
/// examples are set from the start, so full coverage is all ones.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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

    /// The bits at `keep`, packed down in that order: the coverage of the
    /// examples that are left when the others are set aside.
    pub(super) fn select(&self, keep: &[usize]) -> Self {
        let mut selected = Self::from_len(keep.len());
        for (new, &old) in keep.iter().enumerate() {
            if self.get(old) {
                selected.set(new);
            }
        }
        selected
    }

    /// The examples covered, of the first `len`.
    pub(super) fn indices(&self, len: usize) -> Vec<usize> {
        (0..len).filter(|&i| self.get(i)).collect()
    }
}

/// One sub hypothesis and what it proves.
///
/// `u32` counts keep this to 48 bytes; there is one per sub hypothesis.
pub(super) struct HProfile {
    /// Index of the sub hypothesis in [`SearchCtx::hypotheses`].
    pub(super) h: u32,
    /// Positives proved.
    pub(super) n_covered: u32,
    /// Clauses in `h` plus those of every invented predicate it calls.
    pub(super) n_clauses: u32,
    /// Body literals across that same clause set.
    pub(super) n_literals: u32,
    /// The positives it proves.
    pub(super) coverage: Coverage,
    /// The negatives it proves.
    pub(super) neg_coverage: Coverage,
}

impl HProfile {
    /// Profile sub hypothesis `h`, or `None` if it proves more than
    /// `at_most_neg` negatives.
    ///
    /// The examples are proved one after another, from the hypothesis's
    /// `MetaSub`s and those of the definitions it depends on.
    fn new(
        h: u32,
        pos_goals: &[usize],
        neg_goals: &[usize],
        ctx: SearchCtx,
        at_most_neg: usize,
    ) -> Option<Self> {
        let meta_subs = ctx
            .pdt
            .test_meta_subs(ctx.hypotheses.get(h as usize), ctx.heap);

        // Negatives first: a hypothesis over the threshold is dropped
        // without its positives being tried.
        let neg_coverage = proved(neg_goals, &meta_subs, ctx, at_most_neg)?;
        let coverage = proved(pos_goals, &meta_subs, ctx, usize::MAX)?;

        let n_literals: usize = meta_subs
            .iter()
            .map(|meta_sub| meta_sub.template(ctx.predicate_table).body().len())
            .sum();
        Some(Self {
            h,
            n_covered: coverage.count(pos_goals.len()) as u32,
            n_clauses: meta_subs.len() as u32,
            n_literals: n_literals as u32,
            coverage,
            neg_coverage,
        })
    }

    /// This profile over only the positives `pos_keep` and the negatives
    /// `neg_keep`, given by their indices in order.
    pub(super) fn restricted(&self, pos_keep: &[usize], neg_keep: &[usize]) -> Self {
        let coverage = self.coverage.select(pos_keep);
        Self {
            h: self.h,
            n_covered: coverage.count(pos_keep.len()) as u32,
            n_clauses: self.n_clauses,
            n_literals: self.n_literals,
            coverage,
            neg_coverage: self.neg_coverage.select(neg_keep),
        }
    }

    /// The ranking key: most coverage first, then fewest clauses, then --
    /// when `by_literals` -- fewest body literals.
    ///
    /// Coverage is expressed as the number of positives *not* covered so that
    /// every component sorts ascending.
    ///
    /// This exists as one function because two places need the identical key.
    /// [`least_sub_h`] sorts by it, and [`filter_coverage_sub_sets`] breaks
    /// its scan when two profiles share it -- an early exit that is only
    /// sound while it agrees with the order the sort actually produced. The
    /// two disagreed before: the sort used `h.len()` where the break used
    /// `n_clauses`, which counts invented predicates' clauses too.
    pub(super) fn sort_key(
        &self,
        n_pos_examples: usize,
        by_literals: bool,
    ) -> (usize, usize, usize) {
        (
            n_pos_examples - self.n_covered as usize,
            self.n_clauses as usize,
            if by_literals {
                self.n_literals as usize
            } else {
                0
            },
        )
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

/// Which of `goals` the ground clauses `meta_subs` prove, or `None` as soon
/// as more than `at_most` of them are proved.
///
/// `goals` are addresses of goals compiled onto the program heap by
/// [`compile_examples`](super::utils::compile_examples).
fn proved(
    goals: &[usize],
    meta_subs: &[&[usize]],
    ctx: SearchCtx,
    at_most: usize,
) -> Option<Coverage> {
    let config = test_config(ctx.config);
    let mut coverage = Coverage::from_len(goals.len());
    let mut count = 0;
    for (i, &goal) in goals.iter().enumerate() {
        let mut query_heap = QueryHeap::new(ctx.heap, None);
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], meta_subs);
        if proof.prove(&mut query_heap, ctx.predicate_table, config) {
            count += 1;
            if count > at_most {
                return None;
            }
            coverage.set(i);
        }
    }
    Some(coverage)
}

/// Profile every sub hypothesis in [`SearchCtx::hypotheses`], keeping those
/// that prove no negative.
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
pub(super) fn build_profiles(
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Vec<HProfile> {
    let total = u32::try_from(ctx.hypotheses.len()).expect("more than u32::MAX hypotheses");
    let at_most_neg = 0;
    profile_each(
        (0..total).into_par_iter(),
        pos_goals,
        neg_goals,
        ctx,
        at_most_neg,
    )
}

/// Profile the sub hypotheses [`build_profiles`] did not keep, however many
/// negatives they prove. `kept` is its result, still in hypothesis order.
pub(super) fn profile_rest(
    kept: &[HProfile],
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Vec<HProfile> {
    let mut kept = kept.iter().map(|h_profile| h_profile.h).peekable();
    let rest: Vec<u32> = (0..ctx.hypotheses.len() as u32)
        .filter(|h| kept.next_if_eq(h).is_none())
        .collect();
    profile_each(rest.into_par_iter(), pos_goals, neg_goals, ctx, usize::MAX)
}

/// The profiles of `hypotheses`, in order, less those proving more than
/// `at_most_neg` negatives.
fn profile_each(
    hypotheses: impl IndexedParallelIterator<Item = u32>,
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
    at_most_neg: usize,
) -> Vec<HProfile> {
    let total = hypotheses.len();
    let profiled = AtomicUsize::new(0);

    let h_profiles = hypotheses
        .filter_map(|h| {
            let h_profile = HProfile::new(h, pos_goals, neg_goals, ctx, at_most_neg);

            // Throttled: one line per candidate would spend longer painting
            // the terminal than proving the examples.
            let done = profiled.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 256 == 0 || done == total {
                eprint!("\rCoverage: {done}/{total} hypotheses profiled  ");
                let _ = io::stderr().flush();
            }

            h_profile
        })
        .collect();

    eprintln!();
    h_profiles
}

/// Do the ground clauses `meta_subs` prove any negative example?
///
/// For a *combination* of sub hypotheses: two that each prove no negative
/// can together prove one, since a clause from one can resolve against a
/// clause from the other. The negatives are proved in parallel, and the
/// rest are abandoned as soon as one is proved.
pub(super) fn entails_negative(
    neg_goals: &[usize],
    meta_subs: &[&[usize]],
    ctx: SearchCtx,
) -> bool {
    let config = test_config(ctx.config);
    neg_goals.par_iter().any(|&goal| {
        let mut query_heap = QueryHeap::new(ctx.heap, None);
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], meta_subs);
        proof.prove(&mut query_heap, ctx.predicate_table, config)
    })
}

/// A small program and one-clause sub hypotheses over it, for the tests of
/// this module and of the group search.
#[cfg(test)]
pub(super) mod fixture {
    use crate::{
        heap::{Heap, ProgramHeap, Tag::Con, VarReg},
        learners::{
            predicate_unification::PredDefTable, sub_h_comb::SearchCtx, utils::compile_examples,
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
    use super::{build_profiles, entails_negative, fixture::fixture, profile_rest, Coverage};
    use crate::{learners::utils::compile_examples, ParallelConfig};

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

    /// Given `good(d)` and `bad(c)`: sub hypothesis 0 proves the positive
    /// `p(d)`, 1 proves the negative `p(c)`, and 2 proves neither.
    const CLAUSES: [(&str, &str); 3] = [("p", "good"), ("p", "bad"), ("q", "good")];

    #[test]
    fn profiles_record_positive_and_negative_coverage() {
        let mut fixture = fixture(&CLAUSES, &["p(c)."]);
        let pos_goals = compile_examples(&["p(d).".to_string()], &mut fixture.prog_heap);
        let ctx = fixture.ctx(ParallelConfig::default());

        // Those proving no negative are kept, the rest profiled on request.
        let kept = build_profiles(&pos_goals, &fixture.neg_goals, ctx);
        let rest = profile_rest(&kept, &pos_goals, &fixture.neg_goals, ctx);
        let seen = |profiles: &[super::HProfile]| -> Vec<(u32, bool, bool, u32)> {
            profiles
                .iter()
                .map(|p| (p.h, p.coverage.get(0), p.neg_coverage.get(0), p.n_covered))
                .collect()
        };
        assert_eq!(seen(&kept), vec![(0, true, false, 1), (2, false, false, 0)]);
        assert_eq!(seen(&rest), vec![(1, false, true, 0)]);
        assert!(kept.iter().all(|p| p.n_clauses == 1 && p.n_literals == 1));
    }

    #[test]
    fn a_profile_is_restricted_to_the_examples_kept() {
        let mut coverage = Coverage::from_len(4);
        coverage.set(1);
        coverage.set(3);
        // Examples 1 and 3 of four become 0 and 1 of two; then 0 and 2.
        assert!(coverage.select(&[1, 3]).all());
        assert_eq!(coverage.select(&[0, 3]).indices(2), vec![1]);
    }

    #[test]
    fn a_combination_is_checked_against_the_negatives() {
        // Together `p(X):-r(X)` and `r(X):-bad(X)` prove `p(c)`.
        let fixture = fixture(&[("p", "r"), ("r", "bad")], &["p(c)."]);
        let ctx = fixture.ctx(ParallelConfig::default());
        let both = [fixture.hypotheses.get(0), fixture.hypotheses.get(1)];
        let combined = fixture.pdt.union_meta_subs(both, &fixture.prog_heap);
        assert!(entails_negative(&fixture.neg_goals, &combined, ctx));

        let one = fixture
            .pdt
            .union_meta_subs([fixture.hypotheses.get(0)], &fixture.prog_heap);
        assert!(!entails_negative(&fixture.neg_goals, &one, ctx));
    }
}
