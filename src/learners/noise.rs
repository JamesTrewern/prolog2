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

use std::collections::HashSet;

use super::{
    coverage::{profile_rest, HProfile},
    noise_report::{noisy_positives, report_negative, report_positive, NoiseReport, NoisyNegative},
    sub_h_unification::SearchCtx,
};
use crate::heap::{Heap, QueryHeap};

/// Most combinations of choices tried exhaustively; past this the choice
/// is made greedily.
const ENUMERATION_CAP: usize = 1 << 16;
/// Most alternative negative sets kept for one positive, smallest first.
const MAX_SETS: usize = 64;

/// What [`resolve_noise`] found.
pub(super) enum Noise {
    /// Nothing to do: the profiles as they were given.
    Clean(Vec<HProfile>),
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
    /// Indices of the positives left uncovered, in the original examples.
    pub(super) dropped: Vec<usize>,
    /// Indices of the negatives ignored, in the original examples.
    pub(super) ignored: Vec<usize>,
    /// What was set aside, to be printed.
    pub(super) note: String,
}

/// A positive no clean sub hypothesis proves, and the sets of negatives it
/// can be proved with: each set no bigger than it need be, smallest first.
#[derive(Debug)]
struct Conflict {
    pos: usize,
    sets: Vec<u128>,
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

/// Bits below `len`.
fn low_bits(len: usize) -> u128 {
    !u128::MAX.checked_shl(len as u32).unwrap_or(0)
}

/// The set bits, as indices.
fn indices(bits: u128) -> Vec<usize> {
    (0..128).filter(|&i| bits & 1 << i != 0).collect()
}

/// The conflicts among the positives `kept` leaves uncovered, and the
/// positives nothing in `rest` proves either, which no removal recovers.
fn conflicts(
    kept: &[HProfile],
    rest: &[HProfile],
    n_pos: usize,
    n_neg: usize,
) -> (Vec<Conflict>, u128) {
    let covered = kept.iter().fold(0, |all, p| all | p.coverage.0);
    let uncovered = !covered & low_bits(n_pos);

    let mut sets: Vec<HashSet<u128>> = vec![HashSet::new(); n_pos];
    for h_profile in rest {
        let negatives = h_profile.neg_coverage.0 & low_bits(n_neg);
        for pos in indices(h_profile.coverage.0 & uncovered) {
            sets[pos].insert(negatives);
        }
    }

    let mut forced = 0;
    let mut found = Vec::new();
    for pos in indices(uncovered) {
        if sets[pos].is_empty() {
            forced |= 1 << pos;
            continue;
        }
        let mut all: Vec<u128> = sets[pos].iter().copied().collect();
        all.sort_unstable_by_key(|set| (set.count_ones(), *set));
        // A set with another inside it is never the cheaper choice.
        let mut minimal: Vec<u128> = Vec::new();
        for set in all {
            if minimal.len() < MAX_SETS && !minimal.iter().any(|inner| inner & !set == 0) {
                minimal.push(set);
            }
        }
        found.push(Conflict { pos, sets: minimal });
    }
    (found, forced)
}

/// The positives left uncovered when the negatives `ignored` are ignored.
fn dropped_given(conflicts: &[Conflict], forced: u128, ignored: u128) -> u128 {
    conflicts
        .iter()
        .filter(|conflict| !conflict.sets.iter().any(|set| set & !ignored == 0))
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
/// one of its sets) number at most [`ENUMERATION_CAP`]; greedy beyond.
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
                        ignored |= conflict.sets[choice - 1];
                    }
                }
                consider(ignored);
            }
        }
        None => {
            // Keep taking the set that recovers most positives for the
            // negatives it adds, while one pays for itself.
            let mut ignored = 0;
            consider(ignored);
            loop {
                let dropped = dropped_given(conflicts, forced, ignored);
                let next = conflicts
                    .iter()
                    .filter(|conflict| dropped & 1 << conflict.pos != 0)
                    .flat_map(|conflict| conflict.sets.iter().copied())
                    .filter(|set| (ignored | set).count_ones() as usize <= max_ignored)
                    .map(|set| {
                        let added = (set & !ignored).count_ones() as i64;
                        let left = dropped_given(conflicts, forced, ignored | set);
                        let recovered = (dropped & !left).count_ones() as i64;
                        (recovered - added, set)
                    })
                    .filter(|&(gain, _)| gain > 0 || gain == 0 && prefer_ignoring)
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
    let (n_pos, n_neg) = (pos_goals.len(), neg_goals.len());
    let covered = kept.iter().fold(0, |all, p| all | p.coverage.0);
    if covered & low_bits(n_pos) == low_bits(n_pos) {
        return Noise::Clean(kept);
    }

    let rest = profile_rest(&kept, pos_goals, neg_goals, ctx);
    let (conflicts, forced) = conflicts(&kept, &rest, n_pos, n_neg);
    let bounds = (ctx.parallel.pos_noise, ctx.parallel.neg_noise);
    if conflicts.is_empty() && forced.count_ones() as usize > bounds.0 {
        return Noise::Clean(kept);
    }

    match cheapest(&conflicts, forced, bounds, true) {
        Some(removal) => Noise::Filtered(filter(removal, kept, rest, pos_goals, neg_goals, ctx)),
        None => Noise::Failed(failure_report(
            &conflicts, forced, &kept, &rest, pos_goals, neg_goals, ctx,
        )),
    }
}

/// Set the examples of `removal` aside.
fn filter(
    removal: Removal,
    kept: Vec<HProfile>,
    rest: Vec<HProfile>,
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Filtered {
    let (n_pos, n_neg) = (pos_goals.len(), neg_goals.len());
    let pos_keep = indices(!removal.dropped & low_bits(n_pos));
    let neg_keep = indices(!removal.ignored & low_bits(n_neg));

    // Usable now: whatever entails none of the negatives left.
    let recovered = rest
        .iter()
        .filter(|h_profile| h_profile.neg_coverage.0 & low_bits(n_neg) & !removal.ignored == 0);
    let h_profiles: Vec<HProfile> = kept
        .iter()
        .chain(recovered)
        .map(|h_profile| h_profile.restricted(&pos_keep, &neg_keep))
        .collect();

    let heap = QueryHeap::new(ctx.heap, None);
    let mut note = String::new();
    let mut list = |heading: String, goals: &[usize], examples: u128| {
        if examples != 0 {
            note += &format!("{heading}\n");
            for example in indices(examples) {
                note += &format!("\t{}\n", heap.term_string(goals[example]));
            }
        }
    };
    let (pos_noise, neg_noise) = (ctx.parallel.pos_noise, ctx.parallel.neg_noise);
    list(
        format!(
            "Ignoring {} of the {n_neg} negatives as noise (at most {neg_noise})",
            removal.ignored.count_ones()
        ),
        neg_goals,
        removal.ignored,
    );
    let within = kept.iter().fold(0, |all, p| all | p.coverage.0);
    list(
        "Positives entailed as a result".to_string(),
        pos_goals,
        !within & !removal.dropped & low_bits(n_pos),
    );
    list(
        format!(
            "Leaving {} of the {n_pos} positives uncovered as noise (at most {pos_noise})",
            removal.dropped.count_ones()
        ),
        pos_goals,
        removal.dropped,
    );

    Filtered {
        pos_goals: pos_keep.iter().map(|&pos| pos_goals[pos]).collect(),
        neg_goals: neg_keep.iter().map(|&neg| neg_goals[neg]).collect(),
        h_profiles,
        dropped: indices(removal.dropped),
        ignored: indices(removal.ignored),
        note,
    }
}

/// The report for when no removal fits the bounds: on the examples of the
/// cheapest removal there is, bounds aside. When ignoring negatives and
/// leaving positives uncovered come equally cheap, on both.
fn failure_report(
    conflicts: &[Conflict],
    forced: u128,
    kept: &[HProfile],
    rest: &[HProfile],
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> NoiseReport {
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
        indices(examples)
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
    for positive in noisy_positives(kept, rest, pos_goals.len(), neg_goals.len()) {
        if dropped & 1 << positive.pos != 0 {
            report_positive(
                &mut report,
                &positive,
                kept,
                rest,
                pos_goals,
                neg_goals,
                ctx,
            );
        }
    }
    for neg in indices(ignored) {
        // The positives that need it whichever way they are entailed, or
        // failing any, those that need it one way.
        let needing = |every: bool| {
            conflicts
                .iter()
                .filter(|conflict| {
                    let needs = |set: &u128| set & 1 << neg != 0;
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
            blocks: super::coverage::Coverage(blocks),
        };
        report_negative(
            &mut report,
            &negative,
            kept,
            rest,
            pos_goals,
            neg_goals,
            ctx,
        );
    }
    report
}

#[cfg(test)]
mod tests {
    use super::{cheapest, resolve_noise, Conflict, Noise, Removal};
    use crate::{
        learners::noise_report::toy_model::{model, single, Model, BASE},
        ParallelConfig,
    };

    const FREE: (usize, usize) = (usize::MAX, usize::MAX);

    fn removal(ignored: u128, dropped: u128) -> Option<Removal> {
        Some(Removal { ignored, dropped })
    }

    #[test]
    fn one_positive_against_many_negatives_is_the_one_removed() {
        // Positive 0 needs negatives 0..7.
        let conflicts = [Conflict {
            pos: 0,
            sets: vec![0b111_1111],
        }];
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0, 0b1));
    }

    #[test]
    fn one_negative_against_many_positives_is_the_one_removed() {
        // Positives 0, 1 and 2 each need negative 0.
        let conflicts = [0, 1, 2].map(|pos| Conflict {
            pos,
            sets: vec![0b1],
        });
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0b1, 0));
    }

    #[test]
    fn one_against_one_goes_by_the_preference() {
        let conflicts = [Conflict {
            pos: 0,
            sets: vec![0b1],
        }];
        assert_eq!(cheapest(&conflicts, 0, FREE, true), removal(0b1, 0));
        assert_eq!(cheapest(&conflicts, 0, FREE, false), removal(0, 0b1));
    }

    #[test]
    fn the_bounds_can_force_the_dearer_removal_or_none() {
        // Positive 0 needs negatives 0 and 1: cheapest is to leave it.
        let conflicts = [Conflict {
            pos: 0,
            sets: vec![0b11],
        }];
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
            Conflict {
                pos: 0,
                sets: vec![0b01, 0b10],
            },
            Conflict {
                pos: 1,
                sets: vec![0b10],
            },
            Conflict {
                pos: 2,
                sets: vec![0b10],
            },
        ];
        assert_eq!(
            cheapest(&conflicts, 0b1000, FREE, true),
            removal(0b10, 0b1000)
        );
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
        // `m` and `a` would do for p1..p3, but `m` entails n2: use
        // positives the clean hypotheses cover. Here nothing is uncovered
        // only when the model has no p3..p5, so check the opposite too.
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
        assert_eq!(filtered.ignored, vec![0]);
        assert_eq!(filtered.dropped, vec![4]);
        assert_eq!(filtered.pos_goals.len(), 4);
        assert_eq!(filtered.neg_goals.len(), 2);

        // `a`, `b` and `d` are usable, their coverage over p1..p4 and
        // their negatives over n2 and n3.
        let profiles: Vec<(u32, Vec<usize>, Vec<usize>)> = filtered
            .h_profiles
            .iter()
            .map(|p| (p.h, p.coverage.indices(4), p.neg_coverage.indices(2)))
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
        assert!(filtered.ignored.is_empty());
        assert_eq!(filtered.dropped, vec![2, 3, 4]);
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
