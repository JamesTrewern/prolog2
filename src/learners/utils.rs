use std::collections::{HashMap, HashSet};

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use smallvec::SmallVec;

use crate::{
    heap::{Cell, Heap, QueryHeap, SymbolDB},
    parser::{build_clause, tokenise, TokenStream},
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_table::{Predicate, PredicateTable},
    },
    resolution::Proof,
    Config,
};

/// Parse a single example string into a goal on the given query heap.
pub(super) fn parse_example(example: &str, query_heap: &mut QueryHeap) -> Result<usize, String> {
    let literals = TokenStream::new(tokenise(example).map_err(|e| e.to_string())?)
        .parse_goals()
        .map_err(|e| format!("Example '{example}' incorrectly formatted: {e}"))?;
    let heap_id = query_heap.id;
    let clause = build_clause(literals, None, query_heap, Some(heap_id));
    Ok(clause[0])
}
/// Count how many positive examples a set of clauses can prove.
pub(super) fn count_coverage(
    pos_examples: &[String],
    clauses: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    max_depth: usize,
) -> (Vec<bool>, usize) {
    let config = Config {
        max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
        protect_h_preds: false,
    };

    let mut h = Hypothesis::new();
    for clause in clauses {
        h.push_clause((*clause).clone(), SmallVec::new());
    }

    let coverage: Vec<bool> = pos_examples
        .par_iter()
        .map(|example| {
            let mut query_heap = QueryHeap::new(heap, None);
            let goal = match parse_example(example, &mut query_heap) {
                Ok(g) => g,
                Err(_) => return false,
            };
            let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h.clone());
            proof.prove(&mut query_heap, predicate_table, config)
        })
        .collect();

    let count = coverage.iter().filter(|v| **v).count();

    (coverage, count)
}

pub(super) fn union_sub_hypotheses(
    sub_hypotheses: Vec<Vec<Clause>>,
    heap: &Vec<Cell>,
) -> Vec<Clause> {
    let mut top_program = Vec::new();
    let mut seen = HashSet::new();
    for hypothesis in sub_hypotheses {
        for clause in hypothesis {
            let key = clause.to_string(heap);
            if seen.insert(key) {
                top_program.push(clause);
            }
        }
    }
    top_program
}

pub(super) fn collect_used_pred(
    hypothesis: &mut Vec<Clause>,
    heap: &impl Heap,
    predicate_table: &PredicateTable,
) {
    let min_pred_con_id = SymbolDB::set_const("pred_0");
    let mut pred_set = HashMap::new();
    loop {
        let start_len = pred_set.len();
        for clause in hypothesis.iter() {
            for literal in clause.body() {
                if heap[literal + 1].1 > min_pred_con_id {
                    pred_set.insert(heap[literal + 1].1, (heap[*literal].1 - 1, false));
                }
            }
        }
        if start_len == pred_set.len() {
            break;
        }
        for (symbol, (arity, collected)) in pred_set.iter_mut() {
            if !*collected {
                let Predicate::Clauses(clauses) =
                    predicate_table.get_predicate((*symbol, *arity)).unwrap()
                else {
                    panic!();
                };
                hypothesis.extend_from_slice(clauses);
                *collected = true
            }
        }
    }
}
