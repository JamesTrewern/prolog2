use std::{
    collections::{HashMap, HashSet},
    process::ExitCode,
    sync::{
        mpsc::{self, Sender},
    },
    thread,
};

use lazy_static::lazy_static;
use rayon;

use crate::{
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
    },
    parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::build_clause,
        tokeniser::tokenise,
    },
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_table::PredicateTable,
    },
    resolution::proof::Proof,
    Config, Examples,
};

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

/// Message sent from a proof thread to the main thread.
struct HypothesisMsg {
    cells: Vec<Cell>,
    clauses: Vec<Clause>,
}

/// Top Program Construction entry point
pub fn run(
    examples: Examples,
    predicate_table: &PredicateTable,
    heap: &[Cell],
    config: Config,
) -> ExitCode {
    println!("=== Top Program Construction ===");
    println!(
        "Positive examples: {}, Negative examples: {}",
        examples.pos.len(),
        examples.neg.len()
    );

    // let accumulator = generalise(&examples.pos, &predicate_table, &heap, config);

    // // Step 2: Specialise
    // let survived = specialise(&accumulator, &examples.neg, &predicate_table, &heap, config);

    // let surviving_count = survived.iter().filter(|&&b| b).count();
    // let rejected_count = accumulator.hypotheses.len() - surviving_count;
    // println!("\n=== Specialisation Results ===");
    // println!(
    //     "{} hypotheses survived, {} rejected",
    //     surviving_count, rejected_count
    // );

    // // Build final top program from surviving hypotheses
    // println!("\n=== Top Program ===");
    // for (i, (hypothesis, &alive)) in accumulator.hypotheses.iter().zip(survived.iter()).enumerate() {
    //     if alive {
    //         println!("Hypothesis [{}]:", i);
    //         for clause in hypothesis {
    //             println!("  {}", clause.to_string(&accumulator.cells));
    //         }
    //     }
    // }

    // TODO: Step 3 — Reduce

    ExitCode::SUCCESS
}

fn generalise(
    pos_examples: &[String],
    predicate_table: &&PredicateTable,
    heap: &[Cell],
    config: Config,
) {

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT-1)
        .build()
        .unwrap();

    let (tx, rx) = mpsc::channel::<HypothesisMsg>();
}

fn generalise_thread(example: String, predicate_table: &PredicateTable){}
