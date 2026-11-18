//! Deciding which examples are noise.
//!
//! A positive may be entailed only by sub hypotheses that entail negatives
//! too. That is one conflict seen from either end: the positive can be left
//! uncovered, or those negatives can be ignored. [`resolve_noise`] looks for
//! the fewest examples whose removal leaves every remaining positive
//! entailed by a sub hypothesis entailing no remaining negative.
//!
//! The choice is all in the negatives: once a set of them is ignored, the
//! usable sub hypotheses are those entailing no others, and the positives
//! left uncovered are whichever they do not entail. When the cheapest such
//! set fits within [`ParallelConfig::neg_noise`](crate::ParallelConfig) and
//! [`ParallelConfig::pos_noise`](crate::ParallelConfig), the examples are
//! filtered out and the run goes on. When none fits, the examples in the
//! cheapest set are the ones reported on.

use std::collections::HashMap;

use super::{
    coverage::{covered_by, profile_rest, Coverage, HProfile, Profiled},
    noise_report::{report_negative, report_positive, NoiseReport, NoisyNegative},
    sub_h_comb::SearchCtx,
};
use crate::{
    bitflag::BitFlag,
    heap::{Heap, QueryHeap},
};

/// Most combinations of choices tried exhaustively; past this the choice
/// is made greedily.
const ENUMERATION_CAP: usize = 1 << 16;
/// Most alternative negative sets kept for one positive, smallest first.
///
/// Bounds the work of discarding sets that contain another. A positive with
/// more sets than this loses the larger ones silently. That is rarely felt,
/// a larger set never being the cheaper choice for its own positive, but a
/// dropped set may be one shared with other positives. The removal found can
/// then be dearer than the cheapest, set aside a positive that ignoring the
/// chosen negatives would in fact entail, or not be found within the bounds.
const MAX_SETS: usize = 64;

/// What [`resolve_noise`] found.
pub(super) enum Noise {
    /// Nothing to do: the profiles as they were given.
    Clean(Vec<HProfile>),
    /// Nothing to settle, but nothing entails some positives and they are
    /// more than may be left uncovered: the profiles as they were given,
    /// for the cover search to name those positives.
    Uncovered(Vec<HProfile>),
    /// Some examples were set aside.
    Filtered(Filtered),
    /// No removal within the bounds leaves a hypothesis.
    Failed(NoiseReport),
}

/// The examples and profiles left once the noisy examples are set aside.
pub(super) struct Filtered {
    pub(super) pos_goals: Vec<usize>,
    pub(super) neg_goals: Vec<usize>,
    /// The usable sub hypotheses, their coverage over the examples left.
    pub(super) h_profiles: Vec<HProfile>,
    /// What was set aside, to be printed.
    pub(super) note: String,
}

/// A positive no clean sub hypothesis proves, though sub hypotheses
/// entailing negatives do, and the negatives it is proved with.
#[derive(Debug)]
pub(super) struct Conflict {
    /// Index of the positive example.
    pub(super) pos: usize,
    /// How many sub hypotheses prove it.
    pub(super) covering: usize,
    /// The negatives every one of them proves. May be none, when they all
    /// prove some negative but not the same one.
    pub(super) shared: u128,
    /// The sets of negatives it can be proved with, each no bigger than it
    /// need be and smallest first, with the number of sub hypotheses
    /// proving it with exactly that set.
    pub(super) sets: Vec<(u128, usize)>,
}

impl Conflict {
    /// The fewest negatives any sub hypothesis proves alongside it.
    pub(super) fn fewest(&self) -> usize {
        self.sets[0].0.count_ones() as usize
    }

    /// The sets of that many negatives.
    pub(super) fn smallest(&self) -> impl Iterator<Item = (u128, usize)> + '_ {
        let fewest = self.fewest();
        self.sets
            .iter()
            .copied()
            .take_while(move |(set, _)| set.count_ones() as usize == fewest)
    }

    /// Whether some sub hypothesis proves exactly the shared negatives and
    /// no others. When one does, that set is the least any can prove
    /// alongside this positive.
    pub(super) fn shared_is_minimal(&self) -> bool {
        self.smallest().count() == 1 && self.sets[0].0 == self.shared
    }
}

/// Examples to remove, as bits: negatives to ignore and positives to leave
/// uncovered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Removal {
    ignored: u128,
    dropped: u128,
}

impl Removal {
    fn cost(&self) -> u32 {
        self.ignored.count_ones() + self.dropped.count_ones()
    }
}

/// The conflicts among the positives `kept` leaves uncovered, in example
/// order, and the positives nothing in `rest` proves either, which no
/// removal recovers.
pub(super) fn conflicts(profiled: Profiled) -> (Vec<Conflict>, u128) {
    let Profiled { kept, rest, .. } = profiled;
    let (n_pos, n_neg) = (profiled.pos_goals.len(), profiled.neg_goals.len());
    let uncovered = !covered_by(kept) & Coverage::full(n_pos);

    // Per positive: how many prove it, the negatives they all prove, and
    // how many prove it with each set of negatives.
    let mut covering = vec![0; n_pos];
    let mut shared = vec![Coverage::full(n_neg); n_pos];
    let mut sets: Vec<HashMap<u128, usize>> = vec![HashMap::new(); n_pos];
    for h_profile in rest {
        let negatives = h_profile.neg_coverage & Coverage::full(n_neg);
        for pos in (h_profile.coverage & uncovered).indices() {
            covering[pos] += 1;
            shared[pos] &= negatives;
            *sets[pos].entry(negatives).or_default() += 1;
        }
    }

    let mut forced = 0;
    let mut found = Vec::new();
    for pos in uncovered.indices() {
        if covering[pos] == 0 {
            forced |= 1 << pos;
            continue;
        }
        let mut all: Vec<(u128, usize)> = sets[pos].drain().collect();
        all.sort_unstable_by_key(|&(set, _)| (set.count_ones(), set));
        // A set with another inside it is never the cheaper choice.
        let mut minimal: Vec<(u128, usize)> = Vec::new();
        for (set, hypotheses) in all {
            if minimal.len() < MAX_SETS && !minimal.iter().any(|(inner, _)| inner & !set == 0) {
                minimal.push((set, hypotheses));
            }
        }
        found.push(Conflict {
            pos,
            covering: covering[pos],
            shared: shared[pos],
            sets: minimal,
        });
    }
    (found, forced)
}

/// The positives left uncovered when the negatives `ignored` are ignored.
fn dropped_given(conflicts: &[Conflict], forced: u128, ignored: u128) -> u128 {
    conflicts
        .iter()
        .filter(|conflict| !conflict.sets.iter().any(|(set, _)| set & !ignored == 0))
        .fold(forced, |dropped, conflict| dropped | 1 << conflict.pos)
}

/// The removal of fewest examples, of those leaving at most `max_dropped`
/// positives uncovered and ignoring at most `max_ignored` negatives; `None`
/// when there is none.
///
/// Of two removals of the same size, `prefer_ignoring` takes the one
/// ignoring more negatives, and otherwise the one dropping more positives.
///
/// Exact while the combinations of one choice per positive (leave it, or
/// one of its sets) number at most [`ENUMERATION_CAP`], over the sets
/// [`conflicts`] kept (at most [`MAX_SETS`] a positive). Greedy beyond: it
/// stays within the bounds where it can, but may not find the fewest.
fn cheapest(
    conflicts: &[Conflict],
    forced: u128,
    (max_dropped, max_ignored): (usize, usize),
    prefer_ignoring: bool,
) -> Option<Removal> {
    let mut best: Option<Removal> = None;
    let mut consider = |ignored: u128| {
        let removal = Removal {
            ignored,
            dropped: dropped_given(conflicts, forced, ignored),
        };
        if removal.dropped.count_ones() as usize > max_dropped
            || removal.ignored.count_ones() as usize > max_ignored
        {
            return;
        }
        let key = |r: &Removal| {
            let against = match prefer_ignoring {
                true => r.dropped.count_ones(),
                false => r.ignored.count_ones(),
            };
            (r.cost(), against, r.ignored)
        };
        if best.as_ref().is_none_or(|best| key(&removal) < key(best)) {
            best = Some(removal);
        }
    };

    let radices: Vec<usize> = conflicts.iter().map(|c| c.sets.len() + 1).collect();
    let combinations = radices
        .iter()
        .try_fold(1usize, |all, &radix| all.checked_mul(radix))
        .filter(|&all| all <= ENUMERATION_CAP);
    match combinations {
        Some(combinations) => {
            for mut code in 0..combinations {
                let mut ignored = 0;
                for (conflict, &radix) in conflicts.iter().zip(&radices) {
                    let choice = code % radix;
                    code /= radix;
                    if choice > 0 {
                        ignored |= conflict.sets[choice - 1].0;
                    }
                }
                consider(ignored);
            }
        }
        None => {
            // Keep taking the set that recovers most positives for the
            // negatives it adds: while one pays for itself, and whatever it
            // costs while too many positives are still left uncovered.
            let mut ignored = 0;
            consider(ignored);
            loop {
                let dropped = dropped_given(conflicts, forced, ignored);
                let over = dropped.count_ones() as usize > max_dropped;
                let next = conflicts
                    .iter()
                    .filter(|conflict| dropped & 1 << conflict.pos != 0)
                    .flat_map(|conflict| conflict.sets.iter().map(|&(set, _)| set))
                    .filter(|set| (ignored | set).count_ones() as usize <= max_ignored)
                    .map(|set| {
                        let added = (set & !ignored).count_ones() as i64;
                        let left = dropped_given(conflicts, forced, ignored | set);
                        let recovered = (dropped & !left).count_ones() as i64;
                        (recovered - added, set)
                    })
                    .filter(|&(gain, _)| over || gain > 0 || gain == 0 && prefer_ignoring)
                    .max_by_key(|&(gain, set)| (gain, std::cmp::Reverse(set)));
                let Some((_, set)) = next else {
                    break;
                };
                ignored |= set;
                consider(ignored);
            }
        }
    }
    best
}

/// Settle the noise among the examples, given `kept`, the profiles of the
/// sub hypotheses entailing no negative, in hypothesis order.
///
/// When they cover every positive between them there is nothing to settle.
/// Otherwise the other sub hypotheses are profiled, and the fewest examples
/// to remove are looked for within the noise bounds.
///
/// Positives that nothing entails at all are left to the caller to report
/// when they alone exceed the bounds, there being nothing to say of them.
pub(super) fn resolve_noise(
    kept: Vec<HProfile>,
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Noise {
    let n_pos = pos_goals.len();
    if covered_by(&kept) == Coverage::full(n_pos) {
        return Noise::Clean(kept);
    }

    let rest = profile_rest(&kept, pos_goals, neg_goals, ctx);
    let profiled = Profiled {
        kept: &kept,
        rest: &rest,
        pos_goals,
        neg_goals,
        ctx,
    };
    let (conflicts, forced) = conflicts(profiled);
    let bounds = (ctx.parallel.pos_noise, ctx.parallel.neg_noise);
    if conflicts.is_empty() && forced.count_ones() as usize > bounds.0 {
        return Noise::Uncovered(kept);
    }

    match cheapest(&conflicts, forced, bounds, true) {
        Some(removal) => Noise::Filtered(filter(removal, profiled)),
        None => Noise::Failed(failure_report(&conflicts, forced, profiled)),
    }
}

/// Set the examples of `removal` aside.
fn filter(removal: Removal, profiled: Profiled) -> Filtered {
    let Profiled {
        kept,
        rest,
        pos_goals,
        neg_goals,
        ..
    } = profiled;
    let (n_pos, n_neg) = (pos_goals.len(), neg_goals.len());
    let pos_keep = (!removal.dropped & Coverage::full(n_pos)).indices();
    let neg_keep = (!removal.ignored & Coverage::full(n_neg)).indices();

    // Usable now: whatever entails none of the negatives left.
    let recovered = rest
        .iter()
        .filter(|h_profile| h_profile.neg_coverage & Coverage::full(n_neg) & !removal.ignored == 0);
    let h_profiles: Vec<HProfile> = kept
        .iter()
        .chain(recovered)
        .map(|h_profile| h_profile.restricted(&pos_keep, &neg_keep))
        .collect();

    Filtered {
        pos_goals: pos_keep.iter().map(|&pos| pos_goals[pos]).collect(),
        neg_goals: neg_keep.iter().map(|&neg| neg_goals[neg]).collect(),
        h_profiles,
        note: filter_note(removal, profiled),
    }
}

/// What `removal` sets aside and what that gains, to be printed.
fn filter_note(removal: Removal, profiled: Profiled) -> String {
    let Profiled {
        kept,
        pos_goals,
        neg_goals,
        ctx,
        ..
    } = profiled;
    let (n_pos, n_neg) = (pos_goals.len(), neg_goals.len());
    let (pos_noise, neg_noise) = (ctx.parallel.pos_noise, ctx.parallel.neg_noise);

    let heap = QueryHeap::new(ctx.heap, None);
    let mut note = String::new();
    let mut list = |heading: String, goals: &[usize], examples: u128| {
        if examples != 0 {
            note += &format!("{heading}\n");
            for example in examples.indices() {
                note += &format!("\t{}\n", heap.term_string(goals[example]));
            }
        }
    };
    list(
        format!(
            "Ignoring {} of the {n_neg} negatives as noise (at most {neg_noise})",
            removal.ignored.count_ones()
        ),
        neg_goals,
        removal.ignored,
    );
    list(
        "Positives entailed as a result".to_string(),
        pos_goals,
        !covered_by(kept) & !removal.dropped & Coverage::full(n_pos),
    );
    list(
        format!(
            "Leaving {} of the {n_pos} positives uncovered as noise (at most {pos_noise})",
            removal.dropped.count_ones()
        ),
        pos_goals,
        removal.dropped,
    );
    note
}

/// The report for when no removal fits the bounds: on the examples of the
/// cheapest removal there is, bounds aside. When ignoring negatives and
/// leaving positives uncovered come equally cheap, on both.
fn failure_report(conflicts: &[Conflict], forced: u128, profiled: Profiled) -> NoiseReport {
    let Profiled {
        pos_goals,
        neg_goals,
        ctx,
        ..
    } = profiled;
    let unbounded = (usize::MAX, usize::MAX);
    let cheapest_ignoring =
        cheapest(conflicts, forced, unbounded, true).expect("unbounded, so some removal fits");
    let cheapest_dropping =
        cheapest(conflicts, forced, unbounded, false).expect("unbounded, so some removal fits");
    let mut removals = vec![cheapest_ignoring];
    if cheapest_dropping != cheapest_ignoring
        && cheapest_dropping.cost() == cheapest_ignoring.cost()
    {
        removals.push(cheapest_dropping);
    }

    let heap = QueryHeap::new(ctx.heap, None);
    let names = |goals: &[usize], examples: u128| -> Vec<String> {
        examples
            .indices()
            .into_iter()
            .map(|example| heap.term_string(goals[example]))
            .collect()
    };
    let mut report = NoiseReport::new(format!(
        "No hypothesis can be formed leaving at most {} positive(s) uncovered and ignoring at \
         most {} negative(s)",
        ctx.parallel.pos_noise, ctx.parallel.neg_noise
    ));
    for (i, removal) in removals.iter().enumerate() {
        report.line(match (i, removals.len()) {
            (0, 1) => format!("Fewest examples to remove: {}", removal.cost()),
            (0, _) => format!("Fewest examples to remove: {}, either", removal.cost()),
            _ => "or".to_string(),
        });
        if removal.ignored != 0 {
            report.list("Negatives to ignore", names(neg_goals, removal.ignored));
        }
        if removal.dropped != 0 {
            report.list(
                "Positives to leave uncovered",
                names(pos_goals, removal.dropped),
            );
        }
    }
    if forced != 0 {
        report.list(
            "Of those positives, no hypothesis entails",
            names(pos_goals, forced),
        );
    }

    let dropped = removals.iter().fold(0, |all, r| all | r.dropped);
    let ignored = removals.iter().fold(0, |all, r| all | r.ignored);
    for conflict in conflicts {
        if dropped & 1 << conflict.pos != 0 {
            report_positive(&mut report, conflict, profiled);
        }
    }
    for neg in ignored.indices() {
        // The positives that need it whichever way they are entailed, or
        // failing any, those that need it one way.
        let needing = |every: bool| {
            conflicts
                .iter()
                .filter(|conflict| {
                    let needs = |(set, _): &(u128, usize)| set & 1 << neg != 0;
                    match every {
                        true => conflict.sets.iter().all(needs),
                        false => conflict.sets.iter().any(needs),
                    }
                })
                .fold(0, |all, conflict| all | 1 << conflict.pos)
        };
        let blocks = match needing(true) {
            0 => needing(false),
            blocks => blocks,
        };
        let negative = NoisyNegative {
            neg,
            blocks: blocks,
        };
        report_negative(&mut report, &negative, profiled);
    }
    report
}

#[cfg(test)]
mod tests {
    use super::{cheapest, resolve_noise, Conflict, Noise, Removal};
    use crate::bitflag::BitFlag;
    use crate::{
        learners::noise_report::toy_model::{model, single, Model, BASE},
        ParallelConfig,
    };

    const FREE: (usize, usize) = (usize::MAX, usize::MAX);

    /// A conflict with one sub hypothesis for each of `sets`.
    fn conflict(pos: usize, sets: &[u128]) -> Conflict {
        Conflict {
            pos,
            covering: sets.len(),
            shared: sets.iter().fold(u128::MAX, |all, set| all & set),
            sets: sets.iter().map(|&set| (set, 1)).collect(),
        }
    }

    fn removal(ignored: u128, dropped: u128) -> Option<Removal> {
        Some(Removal { ignored, dropped })
    }

    #[test]
    fn one_positive_against_many_negatives_is_the_one_removed() {
        // Positive 0 needs negatives 0..7.
        let conflicts = [conflict(0, &[0b111_1111])];
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0, 0b1));
    }

    #[test]
    fn one_negative_against_many_positives_is_the_one_removed() {
        // Positives 0, 1 and 2 each need negative 0.
        let conflicts = [0, 1, 2].map(|pos| conflict(pos, &[0b1]));
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0b1, 0));
    }

    #[test]
    fn one_against_one_goes_by_the_preference() {
        let conflicts = [conflict(0, &[0b1])];
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0b1, 0));
        assert_eq!(cheapest(&conflicts, 0, FREE, false), removal(0, 0b1));
    }

    #[test]
    fn the_bounds_can_force_the_dearer_removal_or_none() {
        // Positive 0 needs negatives 0 and 1: cheapest is to leave it.
        let conflicts = [conflict(0, &[0b11])];
        assert_eq!(cheapest(&conflicts, 0, (1, 2), true), removal(0, 0b1));
        // No positive may be left, so the two negatives go.
        assert_eq!(cheapest(&conflicts, 0, (0, 2), true), removal(0b11, 0));
        assert_eq!(cheapest(&conflicts, 0, (0, 1), true), None);
    }

    #[test]
    fn overlapping_conflicts_share_the_negatives_they_ignore() {
        // Positive 0 needs negative 0 or negative 1; positives 1 and 2 need
        // negative 1. Ignoring 1 settles all three; positive 3 is beyond
        // help and is left whatever is ignored.
        let conflicts = [
            conflict(0, &[0b01, 0b10]),
            conflict(1, &[0b10]),
            conflict(2, &[0b10]),
        ];
        assert_eq!(
            cheapest(&conflicts, 0b1000, FREE, true),
            removal(0b10, 0b1000)
        );
    }

    /// Seventeen positives each needing three negatives of its own: too
    /// many combinations to enumerate, so the choice is greedy.
    fn many_conflicts() -> Vec<Conflict> {
        (0..17)
            .map(|pos| conflict(pos, &[0b111 << (3 * pos)]))
            .collect()
    }

    #[test]
    fn the_greedy_choice_leaves_what_does_not_pay_for_itself() {
        let all_positives = (1 << 17) - 1;
        assert_eq!(
            cheapest(&many_conflicts(), 0, FREE, true),
            removal(0, all_positives)
        );
    }

    #[test]
    fn the_greedy_choice_pays_what_the_bounds_demand() {
        let conflicts = many_conflicts();
        // No positive may be left: every set is taken, cost what it may.
        let all_negatives = (1 << 51) - 1;
        assert_eq!(
            cheapest(&conflicts, 0, (0, 51), true),
            removal(all_negatives, 0)
        );
        // Five may be left: sets are taken only until five remain.
        let twelve_sets = (1 << 36) - 1;
        let last_five = 0b1_1111 << 12;
        assert_eq!(
            cheapest(&conflicts, 0, (5, usize::MAX), true),
            removal(twelve_sets, last_five)
        );
        // One negative short of covering them all.
        assert_eq!(cheapest(&conflicts, 0, (0, 50), true), None);
    }

    fn resolve(model: Model, pos_noise: usize, neg_noise: usize) -> Noise {
        let parallel = ParallelConfig {
            pos_noise,
            neg_noise,
            ..ParallelConfig::default()
        };
        let ctx = model.fixture.ctx(parallel);
        resolve_noise(model.kept, &model.pos_goals, &model.fixture.neg_goals, ctx)
    }

    #[test]
    fn full_clean_coverage_needs_no_settling() {
        // `a` entails no negative and covers p1 and p2: with only those
        // two as the positives there is nothing to settle.
        let mut model = model(&single(&["a"]));
        model.pos_goals.truncate(2);
        let Noise::Clean(h_profiles) = resolve(model, 0, 0) else {
            panic!("every positive is covered by a clean hypothesis");
        };
        assert_eq!(h_profiles.len(), 1);
    }

    #[test]
    fn positives_nothing_entails_are_left_to_the_cover_search() {
        // With `a` alone p3..p5 are entailed by nothing, so no removal of
        // negatives helps and there is nothing to report on.
        let Noise::Uncovered(h_profiles) = resolve(model(&single(&["a"])), 2, 3) else {
            panic!("three positives are beyond help and only two may be left");
        };
        assert_eq!(h_profiles.len(), 1);
        // Within the bound they are simply left uncovered.
        let Noise::Filtered(filtered) = resolve(model(&single(&["a"])), 3, 0) else {
            panic!("three positives may be left");
        };
        assert_eq!(filtered.pos_goals.len(), 2);
    }

    #[test]
    fn without_noise_allowed_a_conflict_fails() {
        let Noise::Failed(_) = resolve(model(&single(&BASE)), 0, 0) else {
            panic!("p3 and p4 need a negative and p5 is beyond help");
        };
    }

    #[test]
    fn within_the_bounds_the_noisy_examples_are_filtered_out() {
        // Ignoring n1 lets `b` cover p3 and `d` cover p4; p5 nothing covers.
        let Noise::Filtered(filtered) = resolve(model(&single(&BASE)), 1, 1) else {
            panic!("one negative and one positive are enough");
        };
        assert_eq!(filtered.pos_goals.len(), 4);
        assert_eq!(filtered.neg_goals.len(), 2);

        // `a`, `b` and `d` are usable, their coverage over p1..p4 and
        // their negatives over n2 and n3.
        let profiles: Vec<(u32, Vec<usize>, Vec<usize>)> = filtered
            .h_profiles
            .iter()
            .map(|p| (p.h, p.coverage.indices(), p.neg_coverage.indices()))
            .collect();
        assert_eq!(
            profiles,
            vec![
                (0, vec![0, 1], vec![]),
                (1, vec![1, 2], vec![]),
                (3, vec![3], vec![])
            ]
        );
        assert_eq!(
            filtered.note,
            "Ignoring 1 of the 3 negatives as noise (at most 1)\n\
             \tt(n1)\n\
             Positives entailed as a result\n\
             \tt(p3)\n\
             \tt(p4)\n\
             Leaving 1 of the 5 positives uncovered as noise (at most 1)\n\
             \tt(p5)\n"
        );
    }

    #[test]
    fn with_no_negative_to_spare_the_positives_are_left_uncovered() {
        let Noise::Filtered(filtered) = resolve(model(&single(&BASE)), 3, 0) else {
            panic!("three positives are enough");
        };
        assert_eq!(filtered.neg_goals.len(), 3);
        assert_eq!(
            filtered.note,
            "Leaving 3 of the 5 positives uncovered as noise (at most 3)\n\
             \tt(p3)\n\
             \tt(p4)\n\
             \tt(p5)\n"
        );
        let usable: Vec<u32> = filtered.h_profiles.iter().map(|p| p.h).collect();
        assert_eq!(usable, vec![0]);
    }

    #[test]
    fn outside_the_bounds_the_cheapest_removal_is_reported() {
        // p5 has to be left, which no number of negatives makes up for.
        let Noise::Failed(report) = resolve(model(&single(&BASE)), 0, 3) else {
            panic!("p5 cannot be covered");
        };
        let text = report.text();
        assert!(text.starts_with(
            "No hypothesis can be formed leaving at most 0 positive(s) uncovered and ignoring \
             at most 3 negative(s)\n\
             Fewest examples to remove: 2\n\
             Negatives to ignore\n\
             \tt(n1)\n\
             Positives to leave uncovered\n\
             \tt(p5)\n\
             Of those positives, no hypothesis entails\n\
             \tt(p5)\n"
        ));
        // The negative at fault is reported on; p3 only ever comes with it.
        assert!(text.contains(
            "Noisy negative\n\
             \tt(n1)\n\
             Positives only entailed together with it\n\
             \tt(p3)\n"
        ));
        assert!(text.contains("2 hypotheses entail it and no other negative\n"));
        // No positive is: p3 and p4 are recovered by ignoring n1.
        assert!(!text.contains("Noisy positive"));
    }

    #[test]
    fn a_positive_at_fault_gets_the_full_report() {
        // `c` is the one cover of p3, with two negatives: cheaper to leave
        // p3 than to ignore both.
        let Noise::Failed(report) = resolve(model(&single(&["a", "c"])), 0, 0) else {
            panic!("p3 needs two negatives");
        };
        let text = report.text();
        assert!(text.contains("Positives to leave uncovered\n\tt(p3)\n"));
        assert!(text.contains("Noisy positive (entailed by 1 hypothesis)\n\tt(p3)\n"));
        assert!(!text.contains("Noisy negative"));
    }
}
