use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::utils::count_coverage;
use crate::{
    heap::{Cell, Heap, QueryHeap},
    learners::{
        specialise::specialise_h_threaded,
        utils::{collect_used_pred, count_pred_clauses, Coverage},
    },
    parser::{build_clause, tokenise, TokenStream},
    program::{clause::Clause, predicate_table::PredicateTable},
    utils::SubSetIterator,
    Config,
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
    let config = Config {
        max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
        protect_h_preds: false,
    };
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

    eprintln!("Attempting to form top prog from 1 sub hypothesis");
    let single_h_valid: Vec<Vec<Clause>> = h_profiles
        .iter()
        .filter_map(|h_profile| {
            if h_profile.n_covered == pos_examples.len() {
                Some(h_profile.h.to_vec())
            } else {
                None
            }
        })
        .filter(|h| specialise_h_threaded(neg_examples, h, heap, predicate_table, config))
        .collect();

    if !single_h_valid.is_empty() {
        return Some(single_h_valid);
    }

    for n_sub_h in 2..h_profiles.len().min(pos_examples.len() + 1) {
        eprintln!("Attempting to form top prog from {n_sub_h} sub hypotheses");
        if let Some(valid_sub_sets) = find_coverage_groups(&h_profiles, n_sub_h, pos_examples.len())
        {
            //Build grouped hypotheses from indexes
            let mut hs = Vec::new();
            for indexes in &valid_sub_sets {
                let mut h = Vec::new();
                for i in indexes {
                    h.extend(h_profiles[*i].h.iter().map(|c| c.clone()));
                }
                hs.push(h)
            }
            let n_sets = hs.len();
            println!("Found {n_sets} sets of hypotheses covering all positives");
            // Filter any negative entailers
            hs.retain(|h| specialise_h_threaded(neg_examples, h, heap, predicate_table, config));

            if hs.is_empty() {
                println!("No hypotheses sets entailing no negatives");
                continue;
            } else {
                return Some(hs);
            }
        }
    }
    None
}

fn find_uncovered(h_profiles: &Vec<HProfile>, n_pos_examples: usize) -> Option<Vec<usize>> {
    let covered = h_profiles.iter().fold(
        Coverage::from_len(n_pos_examples),
        |acc, HProfile { coverage, .. }| acc.or(coverage),
    );
    let mut not_covered = Vec::new();
    for (i, b) in covered.iter().enumerate() {
        if !b {
            not_covered.push(i);
        }
    }
    (!not_covered.is_empty()).then_some(not_covered)
}

/// Find subsets of coverage groups of size n_sub_h
/// where all positive examples are covered
/// return None if no valid sub sets found
fn find_coverage_groups(
    h_profiles: &[HProfile],
    n_sub_h: usize,
    n_pos_examples: usize,
) -> Option<Vec<Box<[usize]>>> {
    let mut sub_set_coverage = Coverage::from_len(n_pos_examples);

    let mut valid_sub_sets: Vec<Box<[usize]>> = Vec::new();
    let mut ssi = SubSetIterator::new(h_profiles.len(), n_sub_h);
    while let Some(subset) = ssi.next() {
        // halt when 1st added sub h coverage * sub set size is less than the number of examples
        if h_profiles[subset[0]].n_covered * n_sub_h < n_pos_examples {
            break;
        }
        //Skip if coverage sum less than number of examples
        if subset
            .iter()
            .map(|i| h_profiles[*i].n_covered)
            .sum::<usize>()
            < n_pos_examples
        {
            continue;
        }
        sub_set_coverage.fill(false);
        for HProfile { coverage, .. } in subset.iter().map(|i| &h_profiles[*i]) {
            sub_set_coverage = sub_set_coverage.or(coverage);
        }
        if sub_set_coverage.iter().all(|covered| *covered) {
            valid_sub_sets.push(Box::from(subset));
            if valid_sub_sets.len() == MAX_VALID_SUB_SETS {
                return Some(valid_sub_sets);
            }
        }
    }
    (!valid_sub_sets.is_empty()).then_some(valid_sub_sets)
}

/// If any profiles coverage is a sub set of another remove that profile
fn filter_coverage_sub_sets(h_profiles: &mut Vec<HProfile>) {
    let mut filtered = 0;
    for i in (0..h_profiles.len()).rev() {
        let p_i = &h_profiles[i];
        for j in 0..i {
            let p_j = &h_profiles[j];
            if p_i.n_clauses == p_j.n_clauses {
                break;
            }
            if p_i.coverage.sub_set(&p_j.coverage) {
                h_profiles.remove(i);
                filtered += 1;
                break;
            }
        }
    }
    eprintln!("Filtered {filtered} Sub Hypotheses for coverage sub set");
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

mod tests {
    use std::cmp::{Ordering, Reverse};

    #[test]
    fn tuple_order() {
        let mut a = vec![(1, 2), (2, 1), (2, 2), (3, 1)];
        let n = 4;
        a.sort_by_key(|e| (4 - e.0, e.1));
        println!("{a:?}");
    }
}
