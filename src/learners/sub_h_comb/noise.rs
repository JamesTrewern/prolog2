//! The positives that cannot be entailed within the negative noise bound.
//!
//! Once the sub hypotheses are split into those entailing at most
//! [`ParallelConfig::neg_noise`](crate::ParallelConfig) negatives and the
//! rest, a positive that none of the first entails cannot be part of any
//! hypothesis within the bound. [`uncovered`] finds those positives, and
//! [`uncovered_report`] is the report on them.
//!
//! Each such positive that the rest do entail is a [`NoisyPositive`]: the
//! positive and the negatives it comes with.

use super::{
    coverage::{covered_by, Coverage, ExampleSet, Profiled},
    noise_report::{report_positive, within_bound, NoiseReport},
};
use crate::heap::{Heap, QueryHeap};

/// A positive no sub hypothesis within the bound proves, though others do,
/// and the negatives it is proved with.
#[derive(Debug)]
pub(super) struct NoisyPositive<B = Coverage> {
    /// Index of the positive example.
    pub(super) pos: usize,
    /// How many sub hypotheses prove it.
    pub(super) covering: usize,
    /// The negatives every one of them proves. May be none, when they all
    /// prove some negative but not the same one.
    pub(super) shared: B,
    /// The fewest negatives any of them proves.
    pub(super) fewest: usize,
    /// Each distinct set of that many negatives, in order, with the number
    /// of sub hypotheses proving the positive with exactly that set.
    pub(super) smallest: Vec<(B, usize)>,
}

impl<B: ExampleSet> NoisyPositive<B> {
    /// Whether some sub hypothesis proves exactly the shared negatives and
    /// no others. When one does, that set is the least any can prove
    /// alongside this positive.
    pub(super) fn shared_is_minimal(&self) -> bool {
        self.smallest.len() == 1 && self.smallest[0].0 == self.shared
    }
}

/// The positives no sub hypothesis within the bound proves.
pub(super) fn uncovered<B: ExampleSet>(profiled: Profiled<B>) -> B {
    B::full(profiled.pos_goals.len()).difference(&covered_by(profiled.kept))
}

/// The [`uncovered`] positives that something over the bound proves, in
/// example order, and those that nothing proves at all.
pub(super) fn noisy_positives<B: ExampleSet>(profiled: Profiled<B>) -> (Vec<NoisyPositive<B>>, B) {
    let n_neg = profiled.neg_goals.len();
    let uncovered = uncovered(profiled);
    let mut unprovable = B::empty();

    let mut noisy = Vec::new();
    for pos in uncovered.iter() {
        let mut positive = NoisyPositive {
            pos,
            covering: 0,
            shared: B::full(n_neg),
            fewest: usize::MAX,
            smallest: Vec::new(),
        };
        for h_profile in profiled.rest.iter().filter(|p| p.coverage.get(pos)) {
            let negatives = h_profile.neg_coverage;
            positive.covering += 1;
            positive.shared.intersect_with(&negatives);
            if negatives.count() < positive.fewest {
                positive.fewest = negatives.count();
                positive.smallest.clear();
            }
            if negatives.count() == positive.fewest {
                match positive
                    .smallest
                    .iter_mut()
                    .find(|(set, _)| *set == negatives)
                {
                    Some((_, hypotheses)) => *hypotheses += 1,
                    None => positive.smallest.push((negatives, 1)),
                }
            }
        }
        if positive.covering == 0 {
            unprovable.set(pos);
        } else {
            positive.smallest.sort_unstable();
            noisy.push(positive);
        }
    }
    (noisy, unprovable)
}

/// The report on the positives no sub hypothesis within the bound proves:
/// each that the others prove in full, and those nothing proves named.
pub(super) fn uncovered_report<B: ExampleSet>(profiled: Profiled<B>) -> NoiseReport {
    let Profiled { pos_goals, ctx, .. } = profiled;
    let (noisy, unprovable) = noisy_positives(profiled);

    let mut report = NoiseReport::new(format!(
        "{} positive example(s) are entailed by no hypothesis {}",
        noisy.len() + unprovable.count(),
        within_bound(ctx.parallel.neg_noise)
    ));
    if !unprovable.is_empty() {
        let heap = QueryHeap::new(ctx.heap, None);
        report.list(
            "No hypothesis entails",
            unprovable
                .iter()
                .map(|pos| heap.term_string(pos_goals[pos])),
        );
    }
    for positive in &noisy {
        report_positive(&mut report, positive, profiled);
    }
    report
}

#[cfg(test)]
mod tests {
    use super::{uncovered, uncovered_report};
    use crate::{
        bitflag::BitFlag,
        learners::sub_h_comb::{
            coverage::{within, Profiled},
            noise_report::toy_model::{model, single, Model, BASE},
        },
        ParallelConfig,
    };

    /// The model's profiles split at `neg_noise`.
    fn split(model: Model, neg_noise: usize) -> Model {
        let all = model.kept.into_iter().chain(model.rest);
        let mut all: Vec<_> = all.collect();
        all.sort_by_key(|profile| profile.h);
        let (kept, rest) = within(all, neg_noise);
        Model {
            kept,
            rest,
            ..model
        }
    }

    fn profiled(model: &Model, neg_noise: usize) -> Profiled<'_> {
        let parallel = ParallelConfig {
            neg_noise,
            ..ParallelConfig::default()
        };
        Profiled {
            kept: &model.kept,
            rest: &model.rest,
            pos_goals: &model.pos_goals,
            neg_goals: &model.fixture.neg_goals,
            ctx: model.fixture.ctx(parallel),
        }
    }

    #[test]
    fn positives_entailed_only_over_the_bound_are_uncovered() {
        // `a` covers p1 and p2 with no negative. p3 and p4 come with at
        // least one negative, and nothing covers p5.
        let model = split(model(&single(&BASE)), 0);
        assert_eq!(uncovered(profiled(&model, 0)).indices(), vec![2, 3, 4]);
    }

    #[test]
    fn a_wider_bound_leaves_fewer_uncovered() {
        // `b` covers p3 and `d` covers p4, each with the one negative n1.
        let model = split(model(&single(&BASE)), 1);
        assert_eq!(uncovered(profiled(&model, 1)).indices(), vec![4]);
    }

    #[test]
    fn the_report_is_on_each_uncovered_positive() {
        let model = split(model(&single(&BASE)), 0);
        let text = uncovered_report(profiled(&model, 0)).text();
        assert!(text.starts_with(
            "3 positive example(s) are entailed by no hypothesis entailing no negative\n\
             No hypothesis entails\n\
             \tt(p5)\n"
        ));
        assert!(text.contains("Noisy positive (entailed by 2 hypotheses)\n\tt(p3)\n"));
        assert!(text.contains("Noisy positive (entailed by 3 hypotheses)\n\tt(p4)\n"));
    }

    /// The report does not depend on how wide the profiles' sets are.
    #[test]
    fn the_report_is_the_same_at_every_width() {
        use crate::learners::sub_h_comb::coverage::{ExampleSet, HProfile};

        fn narrowed<B: ExampleSet>(profiles: &[HProfile]) -> Vec<HProfile<B>> {
            profiles
                .iter()
                .map(|profile| HProfile {
                    h: profile.h,
                    n_clauses: profile.n_clauses,
                    n_literals: profile.n_literals,
                    coverage: B::from_indices(profile.coverage.iter()),
                    neg_coverage: B::from_indices(profile.neg_coverage.iter()),
                })
                .collect()
        }
        fn text<B: ExampleSet>(model: &Model) -> String {
            let (kept, rest) = (narrowed::<B>(&model.kept), narrowed::<B>(&model.rest));
            uncovered_report(Profiled {
                kept: &kept,
                rest: &rest,
                pos_goals: &model.pos_goals,
                neg_goals: &model.fixture.neg_goals,
                ctx: model.fixture.ctx(ParallelConfig::default()),
            })
            .text()
        }

        let model = split(model(&single(&BASE)), 0);
        let expected = uncovered_report(profiled(&model, 0)).text();
        assert_eq!(text::<u8>(&model), expected);
        assert_eq!(text::<u64>(&model), expected);
        assert_eq!(text::<[u128; 8]>(&model), expected);
    }

    #[test]
    fn the_report_names_the_bound_it_is_within() {
        // Only p5 is left, which nothing entails.
        let model = split(model(&single(&BASE)), 1);
        let text = uncovered_report(profiled(&model, 1)).text();
        assert_eq!(
            text,
            "1 positive example(s) are entailed by no hypothesis entailing at most 1 negative\n\
             No hypothesis entails\n\
             \tt(p5)\n"
        );
    }
}
