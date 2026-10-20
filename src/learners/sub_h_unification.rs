use rayon::iter::{IntoParallelIterator, ParallelIterator};

use super::utils::count_coverage;
use crate::{
    heap::{Cell, Heap, QueryHeap},
    learners::{
        specialise::specialise_h_threaded,
        utils::{collect_used_pred, count_pred_clauses},
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
    let mut h_coverage: Vec<(Box<[Clause]>, Vec<bool>, usize)> = hypotheses
        .into_par_iter()
        .map(|h| {
            let (coverage, count) =
                count_coverage(pos_examples, &h, heap, predicate_table, max_depth);
            (h, coverage, count)
        })
        .collect();

    //Ensure all positives covered by at least 1 hypothesis
    if let Some(uncovered) = find_uncovered(&h_coverage, pos_examples.len()) {
        println!("Some positve examples uncovered:");
        for i in uncovered {
            println!("\t{}", pos_examples[i])
        }
        return None;
    }

    // Sort by coverage count and clause count
    h_coverage.sort_by_cached_key(|(h, _, count)| {
        (
            pos_examples.len() - count,
            h.len() + count_pred_clauses(h, &heap, predicate_table),
        )
    });

    eprintln!("Attempting to form top prog from 1 sub hypothesis");
    let single_h_valid: Vec<Vec<Clause>> = h_coverage
        .iter()
        .filter_map(|(clauses, _, count)| {
            if *count == pos_examples.len() {
                Some(clauses.to_vec())
            } else {
                None
            }
        })
        .filter(|h| specialise_h_threaded(neg_examples, h, heap, predicate_table, config))
        .collect();
    if !single_h_valid.is_empty() {
        return Some(single_h_valid);
    }

    for n_sub_h in 2..h_coverage.len().min(pos_examples.len() + 1) {
        eprintln!("Attempting to form top prog from {n_sub_h} sub hypotheses");
        if let Some(valid_sub_sets) = find_coverage_groups(&h_coverage, n_sub_h, pos_examples.len())
        {
            //Build grouped hypotheses from indexs
            let mut hs = Vec::new();
            for indexes in &valid_sub_sets {
                let mut h = Vec::new();
                for i in indexes {
                    h.extend(h_coverage[*i].0.iter().map(|c| c.clone()));
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

fn find_uncovered(
    h_coverage: &Vec<(Box<[Clause]>, Vec<bool>, usize)>,
    n_pos_examples: usize,
) -> Option<Vec<usize>> {
    let covered = h_coverage.iter().fold(
        vec![false; n_pos_examples].into_boxed_slice(),
        |mut acc, (_, coverage, _)| {
            for (a, c) in acc.iter_mut().zip(coverage.iter()) {
                *a |= c;
            }
            acc
        },
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
    h_coverage: &Vec<(Box<[Clause]>, Vec<bool>, usize)>,
    n_sub_h: usize,
    n_pos_examples: usize,
) -> Option<Vec<Box<[usize]>>> {
    let mut combined_coverage = vec![false; n_pos_examples].into_boxed_slice();

    let mut valid_sub_sets: Vec<Box<[usize]>> = Vec::new();
    let mut ssi = SubSetIterator::new(h_coverage.len(), n_sub_h);
    let mut n = 0;
    while let Some(subset) = ssi.next() {
        // halt when 1st added sub h coverage * sub set size is less than the number of examples
        if h_coverage[subset[0]].2 * n_sub_h < n_pos_examples {
            break;
        }
        //Skip if coverage sum less than number of examples
        if subset.iter().map(|i| h_coverage[*i].2).sum::<usize>() < n_pos_examples {
            continue;
        }
        combined_coverage.fill(false);
        for (_, coverage, _) in subset.iter().map(|i| &h_coverage[*i]) {
            for (combined, h) in combined_coverage.iter_mut().zip(coverage.iter()) {
                *combined |= h
            }
        }
        if combined_coverage.iter().all(|covered| *covered) {
            valid_sub_sets.push(Box::from(subset));
            if valid_sub_sets.len() == MAX_VALID_SUB_SETS {
                return Some(valid_sub_sets);
            }
        }
    }
    (!valid_sub_sets.is_empty()).then_some(valid_sub_sets)
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
