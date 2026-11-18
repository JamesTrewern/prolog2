//! Picking the best of the groups the search found.
//!
//! The [search](super::search) works on bit sets and takes a group to prove
//! the union of what its members prove. That is an estimate. Here each
//! group becomes the hypothesis it stands for, and that hypothesis is
//! profiled by proof, as the sub hypotheses were. The pool is small, around
//! a hundred groups, so each can be treated exactly:
//!
//! 1. build the hypothesis: the group's clauses and the definitions they
//!    depend on;
//! 2. reduce it, when reduction is on;
//! 3. profile it;
//! 4. discard those proving more negatives than the bound, or not every
//!    positive;
//! 5. rank the rest and keep the best.

use rayon::prelude::*;

use super::{
    coverage::{build_profiles, HProfile},
    predicate_unification::PredDefTable,
    search::Group,
    utils::reduce,
    utils::SearchCtx,
};
use crate::{bitflag::BitFlag, program::PackedMetaSubs};

/// The hypotheses chosen from a pool of groups.
pub(super) struct Pool<B> {
    /// Every distinct hypothesis the pool gave, a group of clauses each.
    pub(super) hypotheses: PackedMetaSubs,
    /// The profiles of the best of them, best first. [`HProfile::h`] is an
    /// index in `hypotheses`.
    pub(super) best: Vec<HProfile<B>>,
}

/// The hypotheses of `groups`, profiled by proof, and the best of those
/// that hold up.
///
/// A group is of indices in `profiles`, the profiles of sub hypotheses in
/// `ctx`. `dropped` are the positives being left uncovered as noise, which
/// a hypothesis need not prove.
///
/// The best are those proving fewest negatives, then of fewest clauses,
/// then, with [`ParallelConfig::sort_by_literals`](crate::ParallelConfig),
/// of fewest literals. At most
/// [`ParallelConfig::final_h_count`](crate::ParallelConfig) are kept.
pub(super) fn best_of_pool<B: BitFlag + Send + Sync>(
    groups: &[Group],
    profiles: &[HProfile<B>],
    pos_goals: &[usize],
    neg_goals: &[usize],
    dropped: B,
    ctx: SearchCtx,
) -> Pool<B> {
    // Reduction keeps the positives proved, so is given only those that
    // are to be.
    let wanted: Vec<usize> = (0..pos_goals.len())
        .filter(|&pos| !dropped.get(pos))
        .map(|pos| pos_goals[pos])
        .collect();

    // Build, and reduce, each group's hypothesis.
    let mut built: Vec<Vec<&[usize]>> = groups
        .par_iter()
        .map(|group| {
            let members = group
                .iter()
                .map(|&i| ctx.hypotheses.get(profiles[i].h as usize));
            let hypothesis = ctx.pdt.union_meta_subs(members, ctx.heap).into_vec();
            let mut hypothesis = match ctx.parallel.reduce {
                true => reduce(
                    &wanted,
                    hypothesis,
                    ctx.heap,
                    ctx.predicate_table,
                    ctx.config,
                    false,
                ),
                false => hypothesis,
            };
            // Terms are interned, so equal clauses are equal word for word:
            // in one order, equal hypotheses are equal too.
            hypothesis.sort_unstable();
            hypothesis
        })
        .collect();

    // Different groups can come to the same hypothesis. Keep the first.
    let mut seen = std::collections::HashSet::new();
    built.retain(|hypothesis| seen.insert(hypothesis.clone()));

    let mut hypotheses = PackedMetaSubs::default();
    for hypothesis in &built {
        hypotheses.push(hypothesis.iter().copied());
    }

    // Profile them as sub hypotheses are profiled. The definition table is
    // empty: a hypothesis here holds the clauses of its definitions
    // already, and the real table would put back those reduction removed.
    let no_definitions = PredDefTable::default();
    let finals = SearchCtx::new(
        ctx.heap,
        ctx.predicate_table,
        &hypotheses,
        &no_definitions,
        ctx.config,
        ctx.parallel,
    );
    let mut best: Vec<HProfile<B>> = build_profiles(pos_goals, neg_goals, finals);

    best.retain(|profile| {
        profile.neg_coverage.count() <= ctx.parallel.neg_noise
            && profile.coverage.union(&dropped).is_full(pos_goals.len())
    });
    best.sort_by_key(|profile| {
        let literals = match ctx.parallel.sort_by_literals {
            true => profile.n_literals,
            false => 0,
        };
        (
            profile.neg_coverage.count(),
            profile.n_clauses,
            literals,
            profile.h,
        )
    });
    best.truncate(ctx.parallel.final_h_count);

    Pool { hypotheses, best }
}

#[cfg(test)]
mod tests {
    use super::{best_of_pool, Pool};
    use crate::{
        bitflag::BitFlag,
        learners::{
            coverage::{build_profiles, fixture::fixture, HProfile},
            utils::compile_examples,
        },
        ParallelConfig,
    };

    type Set = u8;

    /// Given `good(d)` and `bad(c)`: sub hypothesis 0 proves `p(d)`, 1
    /// proves `p(c)`, and 2 is of another predicate and proves neither.
    const CLAUSES: [(&str, &str); 3] = [("p", "good"), ("p", "bad"), ("q", "good")];

    /// The best of `groups` for the positives `positives` and the negative
    /// `p(c)`: per hypothesis, its clause count, and the positives and
    /// negatives it proves.
    fn best(
        groups: &[Vec<usize>],
        positives: &[&str],
        dropped: &[usize],
        parallel: ParallelConfig,
    ) -> Vec<(u8, Vec<usize>, Vec<usize>)> {
        let mut fixture = fixture(&CLAUSES, &["p(c)"]);
        let positives: Vec<String> = positives.iter().map(|goal| goal.to_string()).collect();
        let pos_goals = compile_examples(&positives, &mut fixture.prog_heap);
        let ctx = fixture.ctx(parallel);
        let profiles: Vec<HProfile<Set>> = build_profiles(&pos_goals, &fixture.neg_goals, ctx);

        let Pool { hypotheses, best } = best_of_pool(
            groups,
            &profiles,
            &pos_goals,
            &fixture.neg_goals,
            Set::from_indices(dropped.iter().copied()),
            ctx,
        );
        best.iter()
            .map(|profile| {
                // The count is of the clauses the hypothesis holds.
                assert_eq!(
                    hypotheses.get(profile.h as usize).len(),
                    profile.n_clauses as usize
                );
                (
                    profile.n_clauses,
                    profile.coverage.indices(),
                    profile.neg_coverage.indices(),
                )
            })
            .collect()
    }

    fn with(neg_noise: usize, reduce: bool) -> ParallelConfig {
        ParallelConfig {
            neg_noise,
            reduce,
            ..ParallelConfig::default()
        }
    }

    #[test]
    fn the_smaller_hypothesis_comes_first() {
        // `q(X):-good(X)` adds nothing but is not taken out unasked.
        let groups = [vec![0, 2], vec![0]];
        assert_eq!(
            best(&groups, &["p(d)"], &[], with(0, false)),
            vec![(1, vec![0], vec![]), (2, vec![0], vec![])]
        );
    }

    #[test]
    fn reduction_leaves_one_of_two_groups_that_come_to_the_same() {
        let groups = [vec![0, 2], vec![0]];
        assert_eq!(
            best(&groups, &["p(d)"], &[], with(0, true)),
            vec![(1, vec![0], vec![])]
        );
    }

    #[test]
    fn a_hypothesis_over_the_negative_bound_is_discarded() {
        let groups = [vec![0, 1], vec![0]];
        assert_eq!(
            best(&groups, &["p(d)"], &[], with(0, false)),
            vec![(1, vec![0], vec![])]
        );
        // Within the bound it stays, after the one proving no negative.
        assert_eq!(
            best(&groups, &["p(d)"], &[], with(1, false)),
            vec![(1, vec![0], vec![]), (2, vec![0], vec![0])]
        );
    }

    #[test]
    fn a_hypothesis_not_proving_every_positive_is_discarded() {
        // Nothing proves `p(e)`.
        let groups = [vec![0]];
        assert!(best(&groups, &["p(d)", "p(e)"], &[], with(0, false)).is_empty());
        // Unless it is being left uncovered.
        assert_eq!(
            best(&groups, &["p(d)", "p(e)"], &[1], with(0, false)),
            vec![(1, vec![0], vec![])]
        );
        // And reduction then asks only for the positives that are wanted.
        assert_eq!(
            best(&[vec![0, 2]], &["p(d)", "p(e)"], &[1], with(0, true)),
            vec![(1, vec![0], vec![])]
        );
    }

    #[test]
    fn no_more_than_final_h_count_are_kept() {
        let groups = [vec![0], vec![0, 2], vec![0, 1]];
        let parallel = ParallelConfig {
            final_h_count: 2,
            ..with(1, false)
        };
        assert_eq!(best(&groups, &["p(d)"], &[], parallel).len(), 2);
    }
}
