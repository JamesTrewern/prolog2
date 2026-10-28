use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::utils::count_coverage;
use crate::{
    heap::Cell,
    learners::utils::{count_pred_clauses, Coverage},
    program::{clause::Clause, predicate_table::PredicateTable},
};

const MAX_VALID_SUB_SETS: usize = 5;

/// Given a set of sub hypotheses build
/// a hypothesis covering all positives
/// and no negatives
/// with the fewest possible sub h
pub(super) fn least_sub_h(
    pos_examples: &[String],
    neg_examples: &[String],
    hypotheses: Vec<Box<[Clause]>>,
    heap: &[Cell],
    predicate_table: &PredicateTable,
    max_depth: usize,
) -> Option<Vec<Vec<Clause>>> {
    // Count coverage
    let mut h_profiles: Vec<HProfile> = hypotheses
        .into_par_iter()
        .map(|h| HProfile::new(h, pos_examples, heap, predicate_table, max_depth))
        .collect();

    //Ensure all positives covered by at least 1 hypothesis
    if let Some(uncovered) = find_uncovered(&h_profiles, pos_examples.len()) {
        println!("Some positve examples uncovered:");
        for i in uncovered {
            println!("\t{}", pos_examples[i])
        }
        return None;
    }

    // Sort by coverage count and clause count
    h_profiles
        .sort_by_key(|h_profile| (pos_examples.len() - h_profile.n_covered, h_profile.h.len()));
    // Filter any profiles whose coverage is a subset of another profile
    filter_coverage_sub_sets(&mut h_profiles);

    let greedy = greedy_find_coverage_group(&h_profiles);
    let max_k = greedy.len();
    eprintln!("Found full coverage from greedy with {max_k} sub hypotheses");

    let groups: Vec<Vec<Clause>> = if max_k == 1 {
        h_profiles
            .into_iter()
            .filter_map(|profile| {
                if profile.n_covered == pos_examples.len() {
                    Some(profile.h.to_vec())
                } else {
                    None
                }
            })
            .collect()
    } else {
        find_coverage_groups(&h_profiles, max_k, pos_examples.len())
            .into_iter()
            .map(|indexes| {
                indexes
                    .iter()
                    .map(|i| h_profiles[*i].h.clone().to_vec())
                    .flatten()
                    .collect()
            })
            .collect()
    };

    //TODO filter any groups entailing negatives

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
/// return None if no valid sub sets found
fn find_coverage_groups(
    h_profiles: &[HProfile],
    max_k: usize,
    n_pos_examples: usize,
) -> Vec<Box<[usize]>> {
    let no_coverage = Coverage::from_len(n_pos_examples);
    let mut groups = Vec::new();

    let mut group_coverage = h_profiles[0].coverage;
    let mut group = Vec::with_capacity(max_k);
    let mut depth = 1;
    group.push(0);

    let back_track = |group: &mut Vec<usize>, group_coverage: &mut Coverage, depth: &mut usize| {
        if *depth == 0 {
            return false;
        }
        group.pop();
        *group_coverage = no_coverage;
        for i in group {
            **group_coverage |= *h_profiles[*i].coverage;
        }
        *depth -= 1;
        true
    };

    loop {
        let left_to_cover = n_pos_examples - group_coverage.count(n_pos_examples);
        let choices_left = max_k - depth;
        let min_covered = left_to_cover / choices_left;
        // println!("left_to_cover: {left_to_cover}, choices_left: {choices_left}, min_covered: {min_covered}");

        let min_i = *group.get(depth).unwrap_or(&0);
        if let Some(next_i) =
            find_next_choice(h_profiles, min_i, min_covered, group_coverage, &group)
        {
            group_coverage.0 |= h_profiles[next_i].coverage.0;
            if let Some(last_i) = group.get_mut(depth) {
                *last_i = next_i
            } else {
                group.push(next_i);
            }
        } else {
            if back_track(&mut group, &mut group_coverage, &mut depth) {
                continue;
            } else {
                break;
            }
        }

        if group_coverage.all() {
            //Found valid group
            groups.push(group.clone().into_boxed_slice());
            eprintln!("Found Valid Group");
            if groups.len() == MAX_VALID_SUB_SETS {
                break;
            }
            back_track(&mut group, &mut group_coverage, &mut depth);
        } else if depth + 1 == max_k {
            println!(
                "Coverage({}/{n_pos_examples}) at max_k({max_k}), {group:?}",
                group_coverage.count(n_pos_examples)
            );
            if back_track(&mut group, &mut group_coverage, &mut depth) {
                continue;
            } else {
                break;
            }
        } else {
            depth += 1;
        }
    }

    groups
}

/// Search coverage profiles for next valid index, None if no valid
fn find_next_choice(
    h_profiles: &[HProfile],
    min_i: usize,
    min_covered: usize,
    group_coverage: Coverage,
    group: &[usize],
) -> Option<usize> {
    for i in min_i..h_profiles.len() {
        if h_profiles[i].n_covered < min_covered {
            break;
        }
        if group.contains(&i) || h_profiles[i].coverage.difference(&group_coverage) < min_covered {
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
        pos_examples: &[String],
        heap: &[Cell],
        predicate_table: &PredicateTable,
        max_depth: usize,
    ) -> Self {
        let (coverage, n_covered) =
            count_coverage(pos_examples, &h, heap, predicate_table, max_depth);
        let n_clauses = count_pred_clauses(&h, heap, predicate_table) + h.len();
        Self {
            h,
            coverage,
            n_covered,
            n_clauses,
        }
    }
}
