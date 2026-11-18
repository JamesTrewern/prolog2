//! Building groups of sub hypotheses that cover every positive between
//! them, within the negative noise bound.
//!
//! The search works on the profiles' bit sets alone and runs no proofs. A
//! group is taken to prove the union of what its members prove, which is an
//! estimate: the groups found are checked afterwards.
//!
//! It is a greedy choice of the next sub hypothesis with backtracking over
//! the next best choices:
//!
//! - each step scores the candidates and keeps the best
//!   [`BRANCHING_FACTOR`] as its choices ([`Search::step`]);
//! - the first step keeps twice as many, each a starting point, and the
//!   search from each is separate ([`Search::from_start`]);
//! - a choice excludes those taken before it at the same step from
//!   everything below it, so no group is built twice;
//! - once a starting point has given a group, nothing bigger is looked for
//!   from it.
//!
//! [`undominated`] is the filter applied to the sub hypotheses beforehand.

use std::{cmp::Reverse, collections::HashMap, hash::Hash};

use super::coverage::HProfile;
use crate::bitflag::BitFlag;

/// Choices kept at each step; twice as many at the first.
pub(super) const BRANCHING_FACTOR: usize = 10;

/// Most choices taken from one starting point.
// TODO: calibrate. Meant as about a minute for 100,000 sub hypotheses.
pub(super) const MAX_EFFORT: usize = 50_000;

/// A group of sub hypotheses, as their indices in [`Search::profiles`], in
/// the order they were chosen.
pub(super) type Group = Vec<usize>;

/// The size a sub hypothesis is compared by: clauses, then literals when
/// `by_literals`.
fn size<B>(profile: &HProfile<B>, by_literals: bool) -> (u8, u8) {
    let literals = if by_literals { profile.n_literals } else { 0 };
    (profile.n_clauses, literals)
}

/// The sub hypotheses worth searching: `profiles` less every one that
/// another is at least as good as, in their original order.
///
/// `b` is at least as good as `a` when it proves every positive `a` does,
/// proves no negative `a` does not, and is no bigger. Of several that prove
/// exactly the same examples, the smallest is kept, and the first of those.
///
/// The negatives are compared as sets, not counted. A sub hypothesis
/// proving one negative is not dominated by one proving two others: in a
/// group that already proves those two, the second adds none and the first
/// adds one.
pub(super) fn undominated<B: BitFlag + Hash + Eq>(
    profiles: &[HProfile<B>],
    by_literals: bool,
) -> Vec<HProfile<B>> {
    let size = |i: usize| size(&profiles[i], by_literals);

    // The smallest of each set proving exactly the same examples.
    let mut smallest: HashMap<(B, B), usize> = HashMap::new();
    for (i, profile) in profiles.iter().enumerate() {
        let kept = smallest
            .entry((profile.coverage, profile.neg_coverage))
            .or_insert(i);
        if size(i) < size(*kept) {
            *kept = i;
        }
    }

    // Most positives first: only those proving as many can dominate.
    let mut distinct: Vec<(usize, usize)> = smallest
        .into_values()
        .map(|i| (profiles[i].coverage.count(), i))
        .collect();
    distinct.sort_unstable_by_key(|&(positives, i)| (Reverse(positives), i));

    let dominated = |&(positives, a): &(usize, usize)| {
        let (a_profile, a_size) = (&profiles[a], size(a));
        distinct
            .iter()
            .take_while(|&&(others, _)| others >= positives)
            .any(|&(_, b)| {
                let b_profile = &profiles[b];
                b != a
                    && size(b) <= a_size
                    && a_profile.coverage.is_subset(&b_profile.coverage)
                    && b_profile.neg_coverage.is_subset(&a_profile.neg_coverage)
            })
    };
    let mut kept: Vec<usize> = distinct
        .iter()
        .filter(|entry| !dominated(entry))
        .map(|&(_, i)| i)
        .collect();
    kept.sort_unstable();
    kept.into_iter().map(|i| profiles[i]).collect()
}

/// One search for groups.
pub(super) struct Search<'p, B> {
    /// The sub hypotheses to build groups from.
    pub(super) profiles: &'p [HProfile<B>],
    /// How many positives there are.
    pub(super) n_pos: usize,
    /// Most negatives a group may prove.
    pub(super) neg_noise: usize,
    /// Positives taken as covered from the start: those being left
    /// uncovered as noise.
    pub(super) dropped: B,
    /// Most groups taken from one starting point.
    pub(super) per_start: usize,
    /// Whether literals break a tie between sub hypotheses of as many
    /// clauses.
    pub(super) by_literals: bool,
    /// Choices kept at each step, see [`BRANCHING_FACTOR`].
    pub(super) branching: usize,
    /// Most choices taken from one starting point, see [`MAX_EFFORT`].
    pub(super) max_effort: usize,
}

/// One step of building a group: the choices for its next member, and how
/// far through them the search is.
struct Step<B> {
    /// What the group proves before this step's choice.
    covered: B,
    negatives: B,
    /// The candidates to choose from, best first.
    choices: Vec<usize>,
    /// The next of `choices` to take.
    next: usize,
    /// The choice being explored.
    taken: Option<usize>,
    /// The choices explored before it, which are excluded from everything
    /// below this step.
    tried: Vec<usize>,
}

impl<B: BitFlag> Search<'_, B> {
    /// Every group found: from each starting point in turn, at most
    /// [`Self::per_start`] of them.
    ///
    /// Each group covers every positive not in [`Self::dropped`] and proves
    /// at most [`Self::neg_noise`] negatives, going by the bit sets. No
    /// group appears twice, in any order of its members.
    pub(super) fn run(&self) -> Vec<Group> {
        let mut excluded = vec![false; self.profiles.len()];
        let first = self.step(
            self.dropped,
            B::empty(),
            0,
            None,
            2 * self.branching,
            &excluded,
        );

        let mut pool = Vec::new();
        for &start in &first.choices {
            pool.extend(self.from_start(start, &mut excluded));
            // Every group with it has had its chance.
            excluded[start] = true;
        }
        pool
    }

    /// The groups found with `start` as first member. `excluded` is left as
    /// it was given.
    fn from_start(&self, start: usize, excluded: &mut [bool]) -> Vec<Group> {
        let first = &self.profiles[start];
        let covered = self.dropped.union(&first.coverage);
        if covered.is_full(self.n_pos) {
            // Complete on its own: anything added would be redundant.
            return vec![vec![start]];
        }

        let mut found: Vec<Group> = Vec::new();
        // The size of the smallest group found, which later ones may not
        // pass.
        let mut limit: Option<usize> = None;
        let mut effort = 0;
        let mut group: Group = vec![start];
        let mut steps = vec![self.step(
            covered,
            first.neg_coverage,
            group.len(),
            limit,
            self.branching,
            excluded,
        )];

        while found.len() < self.per_start && effort < self.max_effort {
            // Members chosen above this step.
            let members = steps.len();
            let Some(step) = steps.last_mut() else {
                break;
            };
            // Back at this step, its last choice has been explored.
            if let Some(explored) = step.taken.take() {
                excluded[explored] = true;
                step.tried.push(explored);
            }
            let Some(&choice) = step.choices.get(step.next) else {
                // Nothing left to choose: back to the step above.
                for &tried in &step.tried {
                    excluded[tried] = false;
                }
                steps.pop();
                continue;
            };
            step.next += 1;

            let profile = &self.profiles[choice];
            // The limit may have come down since the choices were gathered.
            // A choice passed over this way was not taken, so is not
            // excluded below.
            let left = self.n_pos - step.covered.count();
            let added = profile.coverage.difference_count(&step.covered);
            if limit.is_some_and(|limit| !reaches(added, left, limit.saturating_sub(members))) {
                continue;
            }

            step.taken = Some(choice);
            effort += 1;
            group.truncate(members);
            group.push(choice);
            let covered = step.covered.union(&profile.coverage);
            let negatives = step.negatives.union(&profile.neg_coverage);

            if covered.is_full(self.n_pos) {
                limit = Some(limit.map_or(group.len(), |limit| limit.min(group.len())));
                found.push(group.clone());
            } else {
                let next = self.step(
                    covered,
                    negatives,
                    group.len(),
                    limit,
                    self.branching,
                    excluded,
                );
                steps.push(next);
            }
        }

        for step in &steps {
            for &tried in &step.tried {
                excluded[tried] = false;
            }
        }
        found
    }

    /// The choices for the next member of a group of `members` that proves
    /// `covered` and `negatives`: the best `width` candidates, best first.
    ///
    /// A candidate has to add a positive, stay within what is left of the
    /// negative noise bound, not be `excluded`, and, when there is a size
    /// `limit`, add enough for the group to be finished within it.
    ///
    /// The score of a candidate adding `a` of the `left` positives to cover
    /// and `n` negatives of a remaining `budget` is `a / left - n / budget`,
    /// the second term nothing when it adds no negative. It is compared as
    /// `a * budget - n * left`, which orders the candidates the same way,
    /// `left` and `budget` being the same for all of them. Ties go to the
    /// smaller sub hypothesis, then the earlier.
    fn step(
        &self,
        covered: B,
        negatives: B,
        members: usize,
        limit: Option<usize>,
        width: usize,
        excluded: &[bool],
    ) -> Step<B> {
        let left = self.n_pos - covered.count();
        let budget = self.neg_noise.saturating_sub(negatives.count());
        let places = limit.map(|limit| limit.saturating_sub(members));

        // The best so far, in order.
        let mut best: Vec<((Reverse<i64>, (u8, u8), usize), usize)> = Vec::with_capacity(width + 1);
        for (i, profile) in self.profiles.iter().enumerate() {
            if excluded[i] {
                continue;
            }
            let added = profile.coverage.difference_count(&covered);
            if added == 0 {
                continue;
            }
            let added_neg = profile.neg_coverage.difference_count(&negatives);
            if added_neg > budget {
                continue;
            }
            if places.is_some_and(|places| !reaches(added, left, places)) {
                continue;
            }

            // With no budget left `added_neg` is 0, and the score is the
            // share of the positives alone.
            let score = (added * budget.max(1)) as i64 - (added_neg * left) as i64;
            let rank = (Reverse(score), size(profile, self.by_literals), i);
            if best.len() == width && rank > best[width - 1].0 {
                continue;
            }
            let at = best.partition_point(|(other, _)| *other < rank);
            best.insert(at, (rank, i));
            best.truncate(width);
        }

        Step {
            covered,
            negatives,
            choices: best.into_iter().map(|(_, i)| i).collect(),
            next: 0,
            taken: None,
            tried: Vec::new(),
        }
    }
}

/// Whether a member adding `added` of the `left` positives to cover leaves
/// the group able to be finished in `places` members, itself included.
///
/// It can when it adds at least its share, `left / places`. Passing over one
/// that does not loses no group: of any `places` members covering what is
/// left, one adds at least that share now, and the group is reached through
/// it, with the others still to choose from below.
fn reaches(added: usize, left: usize, places: usize) -> bool {
    added * places >= left
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{undominated, Group, Search, BRANCHING_FACTOR, MAX_EFFORT};
    use crate::{bitflag::BitFlag, learners::sub_h_comb::coverage::HProfile};

    type Set = u8;

    /// Sub hypothesis `h` of one clause proving the positives `pos` and the
    /// negatives `neg`.
    fn profile(h: u32, pos: &[usize], neg: &[usize]) -> HProfile<Set> {
        sized(h, pos, neg, 1, 1)
    }

    fn sized(h: u32, pos: &[usize], neg: &[usize], n_clauses: u8, n_literals: u8) -> HProfile<Set> {
        HProfile {
            h,
            n_clauses,
            n_literals,
            coverage: Set::from_indices(pos.iter().copied()),
            neg_coverage: Set::from_indices(neg.iter().copied()),
        }
    }

    fn search(profiles: &[HProfile<Set>], n_pos: usize, neg_noise: usize) -> Search<'_, Set> {
        Search {
            profiles,
            n_pos,
            neg_noise,
            dropped: Set::empty(),
            per_start: 5,
            by_literals: false,
            branching: BRANCHING_FACTOR,
            max_effort: MAX_EFFORT,
        }
    }

    /// What a group proves, going by the bit sets.
    fn proves(profiles: &[HProfile<Set>], group: &Group) -> (Set, Set) {
        group
            .iter()
            .fold((Set::empty(), Set::empty()), |(pos, neg), &i| {
                (
                    pos.union(&profiles[i].coverage),
                    neg.union(&profiles[i].neg_coverage),
                )
            })
    }

    fn as_sets(groups: &[Group]) -> Vec<BTreeSet<usize>> {
        groups
            .iter()
            .map(|group| group.iter().copied().collect())
            .collect()
    }

    #[test]
    fn the_first_group_is_the_greedy_one() {
        // 0 covers most; of what is left 2 covers more than 1.
        let profiles = [
            profile(0, &[0, 1, 2], &[]),
            profile(1, &[3], &[]),
            profile(2, &[3, 4], &[]),
            profile(3, &[4], &[]),
        ];
        let groups = search(&profiles, 5, 0).run();
        assert_eq!(groups[0], vec![0, 2]);
    }

    #[test]
    fn one_sub_hypothesis_covering_everything_is_a_group_alone() {
        let profiles = [profile(0, &[0, 1], &[]), profile(1, &[0], &[])];
        let groups = search(&profiles, 2, 0).run();
        assert_eq!(groups[0], vec![0]);
        // Nothing is added to a group that is already complete.
        assert!(groups.iter().all(|group| group != &vec![0, 1]));
    }

    /// With every candidate a choice, every cover is found, each once.
    #[test]
    fn no_group_is_built_twice() {
        // Any two of the three cover both positives... except 0 with 0.
        let profiles = [
            profile(0, &[0], &[]),
            profile(1, &[1], &[]),
            profile(2, &[0], &[]),
            profile(3, &[1], &[]),
        ];
        let sets = as_sets(&search(&profiles, 2, 0).run());
        let unique: BTreeSet<_> = sets.iter().cloned().collect();
        assert_eq!(sets.len(), unique.len(), "{sets:?}");
        let expected: BTreeSet<BTreeSet<usize>> = [[0, 1], [0, 3], [1, 2], [2, 3]]
            .into_iter()
            .map(BTreeSet::from)
            .collect();
        assert_eq!(unique, expected);
    }

    #[test]
    fn a_group_stays_within_the_negative_bound() {
        // 1 finishes the cover but proves two negatives; 2 and 3 do it with
        // one between them.
        let profiles = [
            profile(0, &[0], &[]),
            profile(1, &[1, 2], &[0, 1]),
            profile(2, &[1], &[0]),
            profile(3, &[2], &[]),
        ];
        let groups = search(&profiles, 3, 1).run();
        assert!(!groups.is_empty());
        for group in &groups {
            let (pos, neg) = proves(&profiles, group);
            assert!(pos.is_full(3) && neg.count() <= 1, "{group:?}");
        }
        assert!(as_sets(&groups).contains(&BTreeSet::from([0, 2, 3])));

        // With room for both negatives the group proving one is still
        // found first, and the smaller one proving two after it.
        let groups = search(&profiles, 3, 2).run();
        assert_eq!(groups[0], vec![0, 3, 2]);
        assert!(as_sets(&groups).contains(&BTreeSet::from([0, 1])));
        // With room for none there is no cover.
        assert!(search(&profiles, 3, 0).run().is_empty());
    }

    /// A negative costs a share of the budget, weighed against the share of
    /// the positives gained.
    #[test]
    fn the_score_weighs_positives_gained_against_budget_spent() {
        // Of four positives 0 covers three for one negative, 1 covers two
        // for none.
        let profiles = [
            profile(0, &[0, 1, 2], &[0]),
            profile(1, &[0, 1], &[]),
            profile(2, &[2, 3], &[]),
            profile(3, &[3], &[]),
        ];
        // One negative allowed: 3/4 - 1/1 against 2/4 - 0.
        assert_eq!(search(&profiles, 4, 1).run()[0], vec![1, 2]);
        // Four allowed: 3/4 - 1/4 ties 2/4 - 0, and the earlier is taken.
        assert_eq!(search(&profiles, 4, 4).run()[0][0], 0);
        // Eight allowed: 3/4 - 1/8 is the better.
        assert_eq!(search(&profiles, 4, 8).run()[0][0], 0);
    }

    #[test]
    fn a_tie_goes_to_the_smaller_sub_hypothesis() {
        let profiles = [
            sized(0, &[0, 1], &[], 3, 1),
            sized(1, &[0, 1], &[], 2, 9),
            sized(2, &[0, 1], &[], 2, 4),
        ];
        assert_eq!(search(&profiles, 2, 0).run()[0], vec![1]);
        let by_literals = Search {
            by_literals: true,
            ..search(&profiles, 2, 0)
        };
        assert_eq!(by_literals.run()[0], vec![2]);
    }

    /// Once a starting point has given a group, it gives none bigger.
    #[test]
    fn nothing_bigger_than_the_first_group_is_looked_for() {
        // From 0: {0, 1} is found first; {0, 2, 3} also covers, with three.
        let profiles = [
            profile(0, &[0, 1], &[]),
            profile(1, &[2, 3], &[]),
            profile(2, &[2], &[]),
            profile(3, &[3], &[]),
        ];
        let groups = search(&profiles, 4, 0).run();
        assert_eq!(groups[0], vec![0, 1]);
        assert!(!as_sets(&groups).contains(&BTreeSet::from([0, 2, 3])));
    }

    #[test]
    fn a_starting_point_gives_at_most_its_share_of_groups() {
        // 0 with any of the other six covers both positives.
        let mut profiles = vec![profile(0, &[0], &[])];
        profiles.extend((1..7).map(|h| profile(h, &[1], &[])));
        let capped = Search {
            per_start: 2,
            ..search(&profiles, 2, 0)
        };
        let groups = capped.run();
        let from_first = groups.iter().filter(|group| group[0] == 0).count();
        assert_eq!(from_first, 2);
    }

    #[test]
    fn the_effort_from_a_starting_point_is_capped() {
        let mut profiles = vec![profile(0, &[0], &[])];
        profiles.extend((1..7).map(|h| profile(h, &[1], &[])));
        let capped = Search {
            max_effort: 3,
            per_start: usize::MAX,
            ..search(&profiles, 2, 0)
        };
        let from_first = capped.run().iter().filter(|group| group[0] == 0).count();
        assert_eq!(from_first, 3);
    }

    /// Positives being left as noise count as covered from the start.
    #[test]
    fn dropped_positives_need_no_cover() {
        let profiles = [profile(0, &[0, 1], &[]), profile(1, &[0], &[])];
        // Nothing covers the third positive.
        assert!(search(&profiles, 3, 0).run().is_empty());
        let dropping = Search {
            dropped: Set::from_indices([2]),
            ..search(&profiles, 3, 0)
        };
        assert_eq!(dropping.run()[0], vec![0]);
    }

    /// A sub hypothesis is only a choice if it adds a positive.
    #[test]
    fn a_member_always_adds_a_positive() {
        let profiles = [
            profile(0, &[0, 1], &[]),
            profile(1, &[1], &[]),
            profile(2, &[2], &[]),
        ];
        let groups = search(&profiles, 3, 0).run();
        assert!(as_sets(&groups).contains(&BTreeSet::from([0, 2])));
        assert!(!as_sets(&groups).contains(&BTreeSet::from([0, 1, 2])));
    }

    /// A stream of numbers that is the same every run.
    fn numbers() -> impl Iterator<Item = usize> {
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        std::iter::repeat_with(move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as usize
        })
    }

    /// Over many small sets of sub hypotheses, where every candidate is a
    /// choice so nothing is cut off: every group found is a cover within
    /// the bound, none is found twice, and one is found whenever any exists.
    #[test]
    fn small_searches_agree_with_trying_every_group() {
        let mut numbers = numbers();
        for case in 0..300 {
            let (n_pos, n_neg) = (2 + numbers.next().unwrap() % 4, 3);
            let neg_noise = numbers.next().unwrap() % 3;
            let profiles: Vec<HProfile<Set>> = (0..7)
                .map(|h| HProfile {
                    h,
                    n_clauses: 1,
                    n_literals: 1,
                    coverage: (numbers.next().unwrap() % (1 << n_pos)) as Set,
                    neg_coverage: (numbers.next().unwrap() % (1 << n_neg)) as Set,
                })
                .collect();

            let groups = search(&profiles, n_pos, neg_noise).run();
            for group in &groups {
                let (pos, neg) = proves(&profiles, group);
                assert!(pos.is_full(n_pos), "case {case}: {group:?} is no cover");
                assert!(neg.count() <= neg_noise, "case {case}: {group:?} is over");
            }
            let sets = as_sets(&groups);
            let unique: BTreeSet<_> = sets.iter().cloned().collect();
            assert_eq!(sets.len(), unique.len(), "case {case}: {sets:?}");

            // Every subset of the seven, as the bits of a number.
            let exists = (1..1usize << profiles.len()).any(|subset| {
                let group: Group = (0..profiles.len())
                    .filter(|i| subset & 1 << i != 0)
                    .collect();
                let (pos, neg) = proves(&profiles, &group);
                pos.is_full(n_pos) && neg.count() <= neg_noise
            });
            assert_eq!(!groups.is_empty(), exists, "case {case}");
        }
    }

    fn hs(profiles: &[HProfile<Set>]) -> Vec<u32> {
        profiles.iter().map(|profile| profile.h).collect()
    }

    #[test]
    fn of_the_same_positives_the_one_with_more_negatives_goes() {
        let profiles = [
            profile(0, &[0, 1], &[0, 1]),
            profile(1, &[0, 1], &[0]),
            profile(2, &[0, 1], &[1, 2]),
        ];
        // 0 proves every negative 1 does and more. 2 proves a negative 1
        // does not, but 1 proves one that 2 does not: neither goes.
        assert_eq!(hs(&undominated(&profiles, false)), vec![1, 2]);
    }

    #[test]
    fn fewer_positives_with_fewer_negatives_stay() {
        let profiles = [
            profile(0, &[0, 1, 2], &[0]),
            profile(1, &[0, 1], &[]),
            profile(2, &[0], &[0]),
        ];
        // 1 covers less than 0 but proves no negative. 2 covers less than
        // 0 and proves no less.
        assert_eq!(hs(&undominated(&profiles, false)), vec![0, 1]);
    }

    #[test]
    fn of_the_same_examples_the_smallest_stays() {
        let profiles = [
            sized(0, &[0], &[], 2, 2),
            sized(1, &[0], &[], 1, 5),
            sized(2, &[0], &[], 1, 3),
        ];
        assert_eq!(hs(&undominated(&profiles, false)), vec![1]);
        assert_eq!(hs(&undominated(&profiles, true)), vec![2]);
    }

    #[test]
    fn a_bigger_sub_hypothesis_does_not_dominate() {
        let profiles = [sized(0, &[0, 1], &[], 3, 1), sized(1, &[0], &[], 1, 1)];
        assert_eq!(hs(&undominated(&profiles, false)), vec![0, 1]);
    }
}
