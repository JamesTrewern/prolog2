use std::collections::HashSet;

use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::{specialise::clauses_entail_negative, utils::count_coverage};
use crate::{
    heap::{Cell, Heap, QueryHeap},
    learners::utils::{count_pred_clauses, Coverage},
    program::{clause::Clause, predicate_table::PredicateTable},
    Config,
};

const MAX_VALID_SUB_SETS: usize = 5;

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
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
    pred_symbols: &HashSet<usize>,
) -> Option<Vec<SubHGroup>> {
    // Count coverage
    let mut h_profiles: Vec<HProfile> = hypotheses
        .into_par_iter()
        .map(|h| {
            HProfile::new(
                h,
                pos_goals,
                heap,
                predicate_table,
                config.max_depth,
                pred_symbols,
            )
        })
        .collect();

    //Ensure all positives covered by at least 1 hypothesis
    if let Some(uncovered) = find_uncovered(&h_profiles, pos_goals.len()) {
        println!("Some positve examples uncovered:");
        let heap = QueryHeap::new(heap, None);
        for i in uncovered {
            println!("\t{}", heap.term_string(pos_goals[i]))
        }
        return None;
    }

    // Sort by coverage count and clause count
    h_profiles.sort_by_key(|h_profile| (pos_goals.len() - h_profile.n_covered, h_profile.h.len()));
    // Filter any profiles whose coverage is a subset of another profile
    filter_coverage_sub_sets(&mut h_profiles);

    let greedy = greedy_find_coverage_group(&h_profiles);
    let max_k = greedy.len();
    eprintln!("Found full coverage from greedy with {max_k} sub hypotheses");

    let groups: Vec<SubHGroup> = if max_k == 1 {
        // Each group is one sub hypothesis, and every sub hypothesis reaching
        // this point has already been checked against the negatives
        // individually, so there is no combination here to re-check.
        h_profiles
            .into_iter()
            .filter_map(|profile| {
                if profile.n_covered == pos_goals.len() {
                    Some(vec![profile.h.to_vec()])
                } else {
                    None
                }
            })
            .collect()
    } else {
        find_coverage_groups(
            &h_profiles,
            max_k,
            pos_goals.len(),
            neg_goals,
            heap,
            predicate_table,
            config,
        )
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
fn filter_coverage_sub_sets(h_profiles: &mut Vec<HProfile>) {
    let mut filtered = 0;
    for i in (0..h_profiles.len()).rev() {
        let p_i = &h_profiles[i];
        for j in 0..i {
            let p_j = &h_profiles[j];
            if (p_i.n_covered, p_i.n_clauses) == (p_j.n_covered, p_j.n_clauses) {
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
fn find_coverage_groups(
    h_profiles: &[HProfile],
    max_k: usize,
    n_pos_examples: usize,
    neg_goals: &[usize],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
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
            if group_entails_negative(
                h_profiles,
                &group[..=depth],
                neg_goals,
                heap,
                predicate_table,
                config,
            ) {
                rejected += 1;
                eprintln!("Rejected Group (entails a negative)");
            } else {
                groups.push(group[..=depth].to_vec().into_boxed_slice());
                eprintln!("Found Valid Group");
                if groups.len() == MAX_VALID_SUB_SETS {
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
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    let combined: Vec<Clause> = group
        .iter()
        .flat_map(|&i| h_profiles[i].h.iter().cloned())
        .collect();
    clauses_entail_negative(neg_goals, &combined, heap, predicate_table, config)
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
    n_clauses: usize,
}

impl HProfile {
    fn new(
        h: Box<[Clause]>,
        pos_goals: &[usize],
        heap: &[Cell],
        predicate_table: &PredicateTable,
        max_depth: usize,
        pred_symbols: &HashSet<usize>,
    ) -> Self {
        let (coverage, n_covered) = count_coverage(pos_goals, &h, heap, predicate_table, max_depth);
        let n_clauses = count_pred_clauses(&h, heap, predicate_table, pred_symbols) + h.len();
        Self {
            h,
            coverage,
            n_covered,
            n_clauses,
        }
    }
}

#[cfg(test)]
mod coverage_group_tests {
    use super::{find_coverage_groups, HProfile};
    use crate::{
        heap::Cell,
        learners::utils::{compile_examples, Coverage},
        parser::_build_clause,
        program::{clause::Clause, predicate_table::PredicateTable},
        Config,
    };

    fn config() -> Config {
        Config {
            max_depth: 10,
            max_clause: 0,
            debug: false,
            protect_h_preds: false,
        }
    }

    /// A profile with hand-set coverage.
    ///
    /// `find_coverage_groups` only ever reads `coverage`/`n_covered` when
    /// choosing candidates, so fabricating them keeps the fixture to the one
    /// thing under test -- which combinations get built -- while leaving `h`
    /// a real clause list for the negative check to resolve against.
    fn profile(h: Vec<Clause>, covers: &[usize], n_pos: usize) -> HProfile {
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
        }
    }

    /// Two sub hypotheses that are each consistent with the negatives can
    /// still entail one together: `p(X):-r(X)` proves nothing on its own, and
    /// neither does the fact `r(c)`, but combined they prove `p(c)`.
    #[test]
    fn a_group_entailing_a_negative_is_rejected_and_the_search_continues() {
        let mut prog_heap: Vec<Cell> = Vec::new();
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
            &prog_heap,
            &predicate_table,
            config(),
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
        let mut prog_heap: Vec<Cell> = Vec::new();
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
            &prog_heap,
            &predicate_table,
            config(),
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
        let mut prog_heap: Vec<Cell> = Vec::new();
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
            &prog_heap,
            &predicate_table,
            config(),
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
        let mut prog_heap: Vec<Cell> = Vec::new();
        let a = _build_clause(&mut prog_heap, "a(1).");
        let b = _build_clause(&mut prog_heap, "b(1).");

        let h_profiles = vec![profile(vec![a], &[0], 2), profile(vec![b], &[1], 2)];

        let predicate_table = PredicateTable::new();
        let groups = find_coverage_groups(
            &h_profiles,
            2,
            2,
            &[],
            &prog_heap,
            &predicate_table,
            config(),
        );

        let mut sorted: Vec<Vec<usize>> = groups.iter().map(|g| g.to_vec()).collect();
        sorted.sort();
        assert_eq!(sorted, vec![vec![0, 1]]);
    }
}
