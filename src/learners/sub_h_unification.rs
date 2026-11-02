use std::collections::HashSet;

use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::{specialise::clauses_entail_negative, utils::count_coverage};
use crate::{
    heap::{Heap, ProgramHeap, QueryHeap},
    learners::utils::{count_pred_clauses_and_literals, Coverage},
    program::{Clause, PredicateTable},
    Config, ParallelConfig,
};

/// The read-only program context every stage of the group search needs.
///
/// These four travel together through [`least_sub_h`],
/// [`find_coverage_groups`], [`group_entails_negative`] and
/// [`HProfile::new`], so they are passed as one value rather than re-listed
/// at each hop. `Copy`, so handing it on costs nothing.
#[derive(Clone, Copy)]
pub(super) struct SearchCtx<'a> {
    pub(super) heap: &'a ProgramHeap,
    pub(super) predicate_table: &'a PredicateTable,
    pub(super) config: Config,
    pub(super) parallel: ParallelConfig,
}

impl<'a> SearchCtx<'a> {
    pub(super) fn new(
        heap: &'a ProgramHeap,
        predicate_table: &'a PredicateTable,
        config: Config,
        parallel: ParallelConfig,
    ) -> Self {
        Self {
            heap,
            predicate_table,
            config,
            parallel,
        }
    }
}

/// One candidate program, held as the sub hypotheses it was assembled from
/// rather than as a flat clause list.
///
/// Left unflattened so the caller can run
/// [`union_sub_hypotheses`](super::utils::union_sub_hypotheses) over it:
/// two sub hypotheses in a group routinely share clauses, and concatenating
/// them would repeat those.
pub(super) type SubHGroup = Vec<Vec<Clause>>;

/// Given a set of sub hypotheses build
/// a hypothesis covering all positives
/// and no negatives
/// with the fewest possible sub h
pub(super) fn least_sub_h(
    pos_goals: &[usize],
    neg_goals: &[usize],
    hypotheses: Vec<Box<[Clause]>>,
    ctx: SearchCtx,
    pred_symbols: &HashSet<usize>,
) -> Option<Vec<SubHGroup>> {
    // Count coverage
    let mut h_profiles: Vec<HProfile> = hypotheses
        .into_par_iter()
        .map(|h| HProfile::new(h, pos_goals, ctx, pred_symbols))
        .collect();

    //Ensure all positives covered by at least 1 hypothesis
    if let Some(uncovered) = find_uncovered(&h_profiles, pos_goals.len()) {
        println!("Some positve examples uncovered:");
        let heap = QueryHeap::new(ctx.heap, None);
        for i in uncovered {
            println!("\t{}", heap.term_string(pos_goals[i]))
        }
        return None;
    }

    // Sort by coverage count, then clause count, then -- if configured --
    // literal count.
    h_profiles.sort_by_key(|h_profile| {
        h_profile.sort_key(pos_goals.len(), ctx.parallel.sort_by_literals)
    });
    // Filter any profiles whose coverage is a subset of another profile
    filter_coverage_sub_sets(
        &mut h_profiles,
        pos_goals.len(),
        ctx.parallel.sort_by_literals,
    );

    let greedy = greedy_find_coverage_group(&h_profiles);
    let max_k = greedy.len();
    eprintln!("Found full coverage from greedy with {max_k} sub hypotheses");

    let groups: Vec<SubHGroup> = if max_k == 1 {
        // Each group is one sub hypothesis, and every sub hypothesis reaching
        // this point has already been checked against the negatives
        // individually, so there is no combination here to re-check.
        //
        // Capped by `final_h_count` like the combination search below. There
        // can be hundreds of sub hypotheses covering everything on their own,
        // and the caller wants the same number of programs either way.
        h_profiles
            .into_iter()
            .filter(|profile| profile.n_covered == pos_goals.len())
            .take(ctx.parallel.final_h_count)
            .map(|profile| vec![profile.h.to_vec()])
            .collect()
    } else {
        find_coverage_groups(&h_profiles, max_k, pos_goals.len(), neg_goals, ctx)
            .into_iter()
            .map(|indexes| indexes.iter().map(|i| h_profiles[*i].h.to_vec()).collect())
            .collect()
    };

    Some(groups)
}

fn find_uncovered(h_profiles: &Vec<HProfile>, n_pos_examples: usize) -> Option<Vec<usize>> {
    let mut covered = Coverage::from_len(n_pos_examples);

    for HProfile { coverage, .. } in h_profiles {
        *covered |= **coverage;
    }

    if !covered.0 == 0 {
        None
    } else {
        Some((0..n_pos_examples).filter(|i| !covered.get(*i)).collect())
    }
}

/// If any profiles coverage is a sub set of another remove that profile
///
/// `n_pos_examples` and `by_literals` are only here to rebuild the same
/// [`HProfile::sort_key`] the caller sorted by: the scan below stops at the
/// first profile sharing `p_i`'s key, which is only sound while that key is
/// the one that produced the current order.
fn filter_coverage_sub_sets(
    h_profiles: &mut Vec<HProfile>,
    n_pos_examples: usize,
    by_literals: bool,
) {
    let mut filtered = 0;
    for i in (0..h_profiles.len()).rev() {
        let p_i = &h_profiles[i];
        for j in 0..i {
            let p_j = &h_profiles[j];
            if p_i.sort_key(n_pos_examples, by_literals)
                == p_j.sort_key(n_pos_examples, by_literals)
            {
                break;
            }
            if p_i.coverage.sub_set(&p_j.coverage) {
                h_profiles.remove(i);
                filtered += 1;
                break;
            }
        }
    }
    eprintln!(
        "Filtered {filtered} Sub Hypotheses for coverage sub set, {} remaining sub hypotheses",
        h_profiles.len()
    );
}

fn greedy_find_coverage_group(h_profiles: &[HProfile]) -> Vec<usize> {
    let mut res = vec![0];
    let mut covered = h_profiles[0].coverage;
    while !covered.all() {
        let mut best = (0, 0);
        for i in 1..h_profiles.len() {
            if res.contains(&i) || h_profiles[i].coverage.sub_set(&covered) {
                continue;
            }
            let a = h_profiles[i].coverage.difference(&covered);
            if best.0 < a {
                best = (a, i)
            }
        }
        res.push(best.1);
        *covered |= *h_profiles[best.1].coverage;
    }
    res
}

/// Find subsets of coverage groups up to size max_k
///
/// A group is only accepted if it covers every positive example *and* proves
/// no negative. The second check cannot be inherited from the sub hypotheses:
/// each was rejected individually during specialisation, but two sub
/// hypotheses that are each consistent can together entail a negative, since
/// a clause from one can resolve against a clause from the other. A rejected
/// group is backtracked over like any other dead end, so the search carries
/// on looking for a consistent combination of the same size.
///
/// Stops once `final_h_count` groups have been accepted
/// ([`ParallelConfig::final_h_count`]). Each accepted group costs a proof
/// search against every negative, and there are usually far more valid
/// combinations than anyone wants to read.
fn find_coverage_groups(
    h_profiles: &[HProfile],
    max_k: usize,
    n_pos_examples: usize,
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Vec<Box<[usize]>> {
    let no_coverage = Coverage::from_len(n_pos_examples);
    let mut groups = Vec::new();
    let mut rejected = 0;

    let mut group: Vec<usize> = Vec::with_capacity(max_k);
    let mut depth = 0;

    loop {
        let mut prefix_coverage = no_coverage;
        for &i in &group[..depth] {
            *prefix_coverage |= *h_profiles[i].coverage;
        }

        let left_to_cover = n_pos_examples - prefix_coverage.count(n_pos_examples);
        let choices_left = max_k - depth;
        let min_covered = left_to_cover / choices_left;

        // Resume after the previous choice at this level, and start a fresh
        // level after its parent. Indices therefore only ever increase, so
        // each combination is enumerated once instead of once per ordering
        let start = match group.get(depth) {
            Some(&previous) => previous + 1,
            None => group[..depth].last().map_or(0, |&parent| parent + 1),
        };

        let Some(next_i) = find_next_choice(h_profiles, start, min_covered, prefix_coverage) else {
            // Nothing left at this level: drop it and resume the one above.
            group.truncate(depth);
            if depth == 0 {
                break;
            }
            depth -= 1;
            continue;
        };

        if depth < group.len() {
            group[depth] = next_i;
        } else {
            group.push(next_i);
        }

        let mut coverage = prefix_coverage;
        *coverage |= *h_profiles[next_i].coverage;

        if coverage.all() {
            // Covers every positive; it is only a valid group if the
            // combination also proves no negative.
            if group_entails_negative(h_profiles, &group[..=depth], neg_goals, ctx) {
                rejected += 1;
                eprintln!("Rejected Group (entails a negative)");
            } else {
                groups.push(group[..=depth].to_vec().into_boxed_slice());
                eprintln!("Found Valid Group");
                if groups.len() == ctx.parallel.final_h_count {
                    break;
                }
            }
            // Stay at this level; the next pass resumes after `next_i`.
            continue;
        }

        if depth + 1 == max_k {
            // No room for another choice, so this prefix cannot be completed.
            continue;
        }

        depth += 1;
    }

    if rejected > 0 {
        eprintln!("Rejected {rejected} coverage groups entailing a negative");
    }

    groups
}

/// Does the union of a group's sub hypotheses prove any negative example?
fn group_entails_negative(
    h_profiles: &[HProfile],
    group: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> bool {
    let combined: Vec<Clause> = group
        .iter()
        .flat_map(|&i| h_profiles[i].h.iter().cloned())
        .collect();
    clauses_entail_negative(
        neg_goals,
        &combined,
        ctx.heap,
        ctx.predicate_table,
        ctx.config,
    )
}

/// Search coverage profiles for next valid index, None if no valid
fn find_next_choice(
    h_profiles: &[HProfile],
    start: usize,
    min_covered: usize,
    prefix_coverage: Coverage,
) -> Option<usize> {
    for i in start..h_profiles.len() {
        // Profiles are sorted by descending coverage, so once one is too
        // small every later one is too.
        if h_profiles[i].n_covered < min_covered {
            break;
        }
        if h_profiles[i].coverage.difference(&prefix_coverage) < min_covered {
            continue;
        }
        return Some(i);
    }
    None
}

struct HProfile {
    h: Box<[Clause]>,
    coverage: Coverage,
    n_covered: usize,
    /// Clauses in `h` plus those of every invented predicate it calls.
    n_clauses: usize,
    /// Body literals across that same clause set.
    n_literals: usize,
}

impl HProfile {
    fn new(
        h: Box<[Clause]>,
        pos_goals: &[usize],
        ctx: SearchCtx,
        pred_symbols: &HashSet<usize>,
    ) -> Self {
        let (coverage, n_covered) = count_coverage(
            pos_goals,
            &h,
            ctx.heap,
            ctx.predicate_table,
            ctx.config.max_depth,
        );
        let (pred_clauses, pred_literals) =
            count_pred_clauses_and_literals(&h, ctx.heap, ctx.predicate_table, pred_symbols);
        let n_clauses = pred_clauses + h.len();
        let n_literals = pred_literals + h.iter().map(|clause| clause.body().len()).sum::<usize>();
        Self {
            h,
            coverage,
            n_covered,
            n_clauses,
            n_literals,
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
    fn sort_key(&self, n_pos_examples: usize, by_literals: bool) -> (usize, usize, usize) {
        (
            n_pos_examples - self.n_covered,
            self.n_clauses,
            if by_literals { self.n_literals } else { 0 },
        )
    }
}

#[cfg(test)]
mod coverage_group_tests {
    use super::{find_coverage_groups, HProfile, SearchCtx};
    use crate::heap::ProgramHeap;
    use crate::{
        learners::utils::{compile_examples, Coverage},
        parser::_build_clause,
        program::{Clause, PredicateTable},
        Config, ParallelConfig,
    };

    /// `max_clause` is left at the default: the proofs these tests drive are
    /// built with `Proof::without_learning`, so the hypothesis size limit
    /// never comes into it.
    fn config() -> Config {
        Config {
            max_depth: 10,
            debug: false,
            protect_h_preds: false,
            ..Config::default()
        }
    }

    /// A cap high enough that these tests never hit it -- they are about
    /// which combinations get built, not about where the search stops.
    const MANY_GROUPS: usize = 100;

    /// A [`SearchCtx`] over `prog_heap` returning at most `final_h_count`
    /// groups.
    fn ctx<'a>(
        prog_heap: &'a ProgramHeap,
        predicate_table: &'a PredicateTable,
        final_h_count: usize,
    ) -> SearchCtx<'a> {
        SearchCtx::new(
            prog_heap,
            predicate_table,
            config(),
            ParallelConfig {
                final_h_count,
                ..ParallelConfig::default()
            },
        )
    }

    /// A profile with hand-set coverage.
    ///
    /// `find_coverage_groups` only ever reads `coverage`/`n_covered` when
    /// choosing candidates, so fabricating them keeps the fixture to the one
    /// thing under test -- which combinations get built -- while leaving `h`
    /// a real clause list for the negative check to resolve against.
    fn profile(h: Vec<Clause>, covers: &[usize], n_pos: usize) -> HProfile {
        let n_literals = h.iter().map(|clause| clause.body().len()).sum();
        profile_with_literals(h, covers, n_pos, n_literals)
    }

    /// As [`profile`], but with the literal count set by hand, for the
    /// tiebreaker tests where the clause lists are deliberately the same size.
    pub(super) fn profile_with_literals(
        h: Vec<Clause>,
        covers: &[usize],
        n_pos: usize,
        n_literals: usize,
    ) -> HProfile {
        let mut coverage = Coverage::from_len(n_pos);
        for &i in covers {
            coverage.set(i);
        }
        let n_clauses = h.len();
        HProfile {
            h: h.into_boxed_slice(),
            coverage,
            n_covered: covers.len(),
            n_clauses,
            n_literals,
        }
    }

    /// Two sub hypotheses that are each consistent with the negatives can
    /// still entail one together: `p(X):-r(X)` proves nothing on its own, and
    /// neither does the fact `r(c)`, but combined they prove `p(c)`.
    #[test]
    fn a_group_entailing_a_negative_is_rejected_and_the_search_continues() {
        let mut prog_heap = ProgramHeap::new();
        let rule = _build_clause(&mut prog_heap, "p(X):-r(X).");
        let bad_fact = _build_clause(&mut prog_heap, "r(c).");
        let good_fact = _build_clause(&mut prog_heap, "r(d).");
        let neg_goals = compile_examples(&["p(c).".to_string()], &mut prog_heap);

        // Two positives: profile 0 covers the first, profiles 1 and 2 the
        // second, so either pairing is a complete cover.
        let h_profiles = vec![
            profile(vec![rule], &[0], 2),
            profile(vec![bad_fact], &[1], 2),
            profile(vec![good_fact], &[1], 2),
        ];

        let predicate_table = PredicateTable::new();
        let groups = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &neg_goals,
            ctx(&prog_heap, &predicate_table, MANY_GROUPS),
        );

        assert!(
            !groups.iter().any(|group| &**group == [0, 1]),
            "group [0,1] proves the negative p(c) and must be rejected"
        );
        assert!(
            groups.iter().any(|group| &**group == [0, 2]),
            "the search must carry on past the rejection and find [0,2]"
        );
    }

    /// The same search with no negatives keeps both complete covers, so the
    /// rejection above is attributable to the negative and not to the group
    /// being unreachable.
    #[test]
    fn without_negatives_both_covers_are_kept() {
        let mut prog_heap = ProgramHeap::new();
        let rule = _build_clause(&mut prog_heap, "p(X):-r(X).");
        let bad_fact = _build_clause(&mut prog_heap, "r(c).");
        let good_fact = _build_clause(&mut prog_heap, "r(d).");

        let h_profiles = vec![
            profile(vec![rule], &[0], 2),
            profile(vec![bad_fact], &[1], 2),
            profile(vec![good_fact], &[1], 2),
        ];

        let predicate_table = PredicateTable::new();
        let groups = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &[],
            ctx(&prog_heap, &predicate_table, MANY_GROUPS),
        );

        assert!(groups.iter().any(|group| &**group == [0, 1]));
        assert!(groups.iter().any(|group| &**group == [0, 2]));
    }

    /// Every returned group must actually cover every positive.
    ///
    /// The search used to report groups that did not: on backtracking it
    /// overwrote the choice at the restored level while leaving that choice's
    /// bits in the running coverage, so the replacement inherited them and a
    /// one-profile group could look like a complete cover.
    #[test]
    fn returned_groups_are_complete_covers() {
        let mut prog_heap = ProgramHeap::new();
        let a = _build_clause(&mut prog_heap, "a(1).");
        let b = _build_clause(&mut prog_heap, "b(1).");
        let c = _build_clause(&mut prog_heap, "c(1).");

        // No single profile covers both positives, so any one-element group
        // in the output is a bug rather than a legitimate answer.
        let h_profiles = vec![
            profile(vec![a], &[0], 2),
            profile(vec![b], &[1], 2),
            profile(vec![c], &[1], 2),
        ];

        let predicate_table = PredicateTable::new();
        let groups = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &[],
            ctx(&prog_heap, &predicate_table, MANY_GROUPS),
        );

        assert!(!groups.is_empty());
        for group in &groups {
            let mut coverage = Coverage::from_len(2);
            for &i in group.iter() {
                *coverage |= *h_profiles[i].coverage;
            }
            assert!(
                coverage.all(),
                "group {group:?} was returned but does not cover every positive"
            );
        }
    }

    /// Combinations are enumerated once, not once per ordering -- each
    /// complete group now costs a proof search against every negative.
    #[test]
    fn groups_are_not_repeated_in_a_different_order() {
        let mut prog_heap = ProgramHeap::new();
        let a = _build_clause(&mut prog_heap, "a(1).");
        let b = _build_clause(&mut prog_heap, "b(1).");

        let h_profiles = vec![profile(vec![a], &[0], 2), profile(vec![b], &[1], 2)];

        let predicate_table = PredicateTable::new();
        let groups = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &[],
            ctx(&prog_heap, &predicate_table, MANY_GROUPS),
        );

        let mut sorted: Vec<Vec<usize>> = groups.iter().map(|g| g.to_vec()).collect();
        sorted.sort();
        assert_eq!(sorted, vec![vec![0, 1]]);
    }

    /// The search stops once `final_h_count` groups have been accepted.
    ///
    /// Four profiles each covering one of two positives give four complete
    /// covers -- [0,2], [0,3], [1,2], [1,3] -- so a cap below that is
    /// observable.
    #[test]
    fn the_search_stops_at_final_h_count() {
        let mut prog_heap = ProgramHeap::new();
        let clause = _build_clause(&mut prog_heap, "a(1).");
        let h_profiles = vec![
            profile(vec![clause.clone()], &[0], 2),
            profile(vec![clause.clone()], &[0], 2),
            profile(vec![clause.clone()], &[1], 2),
            profile(vec![clause], &[1], 2),
        ];
        let predicate_table = PredicateTable::new();

        let uncapped = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &[],
            ctx(&prog_heap, &predicate_table, MANY_GROUPS),
        );
        assert!(
            uncapped.len() > 2,
            "fixture must offer more covers than the cap below, got {}",
            uncapped.len()
        );

        for cap in [1, 2] {
            let capped = find_coverage_groups(
                &h_profiles,
                2,
                2,
                &[],
                ctx(&prog_heap, &predicate_table, cap),
            );
            assert_eq!(capped.len(), cap, "a cap of {cap} must return {cap} groups");
        }
    }
}

#[cfg(test)]
mod sort_key_tests {
    use super::coverage_group_tests::profile_with_literals;
    use crate::parser::_build_clause;

    use crate::heap::ProgramHeap;

    /// Two candidates with the same coverage and the same clause count are
    /// ordered by literal count -- but only with the flag set.
    #[test]
    fn literals_break_a_tie_only_when_enabled() {
        let mut prog_heap = ProgramHeap::new();
        let short = _build_clause(&mut prog_heap, "p(X):-q(X).");
        let long = _build_clause(&mut prog_heap, "p(X):-q(X),r(X),s(X).");

        let wordy = profile_with_literals(vec![long], &[0], 1, 3);
        let terse = profile_with_literals(vec![short], &[0], 1, 1);

        assert!(
            terse.sort_key(1, true) < wordy.sort_key(1, true),
            "with the flag on, the hypothesis with fewer literals sorts first"
        );
        assert_eq!(
            terse.sort_key(1, false),
            wordy.sort_key(1, false),
            "with the flag off the two must still tie, so existing setups rank as before"
        );
    }

    /// The tiebreaker is only ever a tiebreaker: it must not let a program
    /// with fewer literals outrank one that covers more, or one that is
    /// smaller.
    #[test]
    fn literals_never_outweigh_coverage_or_clause_count() {
        let mut prog_heap = ProgramHeap::new();
        let clause = _build_clause(&mut prog_heap, "p(X):-q(X).");

        // Covers one of two positives with a single literal.
        let narrow = profile_with_literals(vec![clause.clone()], &[0], 2, 1);
        // Covers both, but with far more literals.
        let broad = profile_with_literals(vec![clause.clone()], &[0, 1], 2, 99);
        assert!(
            broad.sort_key(2, true) < narrow.sort_key(2, true),
            "coverage dominates literal count"
        );

        // Same coverage, one clause vs two, and the bigger program is terser.
        let one_clause = profile_with_literals(vec![clause.clone()], &[0], 1, 9);
        let two_clauses = profile_with_literals(vec![clause.clone(), clause], &[0], 1, 1);
        assert!(
            one_clause.sort_key(1, true) < two_clauses.sort_key(1, true),
            "clause count dominates literal count"
        );
    }
}
