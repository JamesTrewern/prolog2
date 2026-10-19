use super::utils::{count_coverage, parse_example, union_sub_hypotheses};
use crate::{
    heap::{Cell, QueryHeap},
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use smallvec::SmallVec;
use std::io::{self, Write};

pub(super) fn reduce_hypotheses(
    pos_examples: &[String],
    sub_hypotheses: Vec<Vec<Clause>>,
    heap: &Vec<Cell>,
    predicate_table: &PredicateTable,
    config: Config,
) -> Vec<Clause> {
    // Step 2b: Per-hypothesis reduction — remove redundant clauses within each
    // sub-hypothesis before union, so specific clauses don't drown out general ones.

    let sub_total = sub_hypotheses.len();

    // Reduce each sub-hypothesis and score by coverage (number of positives entailed)
    let mut scored: Vec<(usize, Vec<Clause>)> = Vec::new();
    for (idx, hypothesis) in sub_hypotheses.into_iter().enumerate() {
        eprint!("\rSub-reduce: {}/{sub_total}    ", idx + 1);
        let _ = io::stderr().flush();
        let reduced = reduce(
            pos_examples,
            hypothesis,
            &heap,
            predicate_table,
            config,
            false,
        );
        let coverage = count_coverage(
            pos_examples,
            &reduced,
            &heap,
            predicate_table,
            config.max_depth,
        );
        scored.push((coverage.1, reduced));
    }
    eprintln!("\rSub-reduce: {sub_total}/{sub_total} ...done    ");

    // Sort by coverage ascending — specific hypotheses first in the union.
    // Plotkin's reduction checks clauses front-to-back: specific clauses get
    // checked first and removed (the general ones behind them cover the same
    // examples). By the time we reach the general clauses, the specific ones
    // are gone and the general ones become essential.
    scored.sort_by(|a, b| a.0.cmp(&b.0));

    // Union all reduced sub-hypothesis clauses, deduplicated
    let top_program = union_sub_hypotheses(scored.into_iter().map(|(_, h)| h).collect(), heap);

    println!("\n=== Top Program ({} clauses) ===", top_program.len());
    for clause in &top_program {
        println!("  {}", clause.to_string(heap));
    }

    // Step 3: Final reduction on the union
    reduce(
        pos_examples,
        top_program,
        &heap,
        predicate_table,
        config,
        true,
    )
}

/// Plotkin's program reduction (Algorithm 3).
/// Sequentially tries removing each clause; if all positives are still provable
/// without it, the clause is redundant and permanently removed.
pub(super) fn reduce<'a>(
    pos_examples: &[String],
    mut hypothesis: Vec<Clause>,
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
    verbose: bool,
) -> Vec<Clause> {
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    // New reduction method
    // pop clause
    // check coverage if same continue
    // if less coverage add clause to front (design vec with easy front adding)
    // loop until clauses_considered == initial size

    let total = hypothesis.len();
    let mut removed = 0usize;
    let mut i = 0;
    while i < hypothesis.len() {
        if verbose {
            eprint!(
                "\rReduce: {}/{total} checked, {removed} removed    ",
                i + removed + 1
            );
            let _ = io::stderr().flush();
        }

        // Build hypothesis from all clauses except the one at index i
        let mut h = Hypothesis::new();
        for (j, clause) in hypothesis.iter().enumerate() {
            if j != i {
                h.push_clause((*clause).clone(), SmallVec::new());
            }
        }

        // Check if all positive examples are still provable without clause i
        let redundant = pos_examples.iter().all(|example| {
            let mut query_heap = QueryHeap::new(heap, None);
            let goal = match parse_example(example, &mut query_heap) {
                Ok(g) => g,
                Err(_) => return true, // skip unparseable examples
            };
            let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h.clone());
            proof.prove(&mut query_heap, predicate_table, config)
        });

        if redundant {
            hypothesis.remove(i);
            removed += 1;
            // Don't increment i — next clause slides into this position
        } else {
            i += 1;
        }
    }
    if verbose {
        eprintln!(" ...done");
    }

    hypothesis
}
