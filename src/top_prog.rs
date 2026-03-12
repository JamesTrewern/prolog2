use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    process::ExitCode,
    sync::{
        Arc, atomic::{AtomicUsize, Ordering}, mpsc::{self, Sender}
    },
    thread, usize,
};

use lazy_static::lazy_static;
use rayon;
use smallvec::SmallVec;

use crate::{
    Config, Examples, heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
    }, parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::build_clause,
        tokeniser::tokenise,
    }, program::{clause::Clause, hypothesis::{self, Hypothesis}, predicate_table::PredicateTable}, resolution::proof::Proof
};

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

/// Message sent from a proof thread to the main thread.
struct HypothesisMsg {
    cells: Vec<Cell>,
    h: Vec<Clause>,
}

/// Top Program Construction entry point
pub fn run(
    examples: Examples,
    predicate_table: &PredicateTable,
    mut heap: Vec<Cell>,
    config: Config,
) -> ExitCode {
    println!("=== Top Program Construction ===");
    println!(
        "Positive examples: {}, Negative examples: {}",
        examples.pos.len(),
        examples.neg.len()
    );

    // Step 1: Generalise
    let (cells, hypotheses) = generalise(&examples.pos, predicate_table, &heap, config);
    heap.extend_from_slice(&cells);

    println!(
        "\n=== Generalisation Results ===\n{} unique hypotheses, {} heap cells",
        hypotheses.len(),
        cells.len()
    );

    // Step 2: Specialise
    let retained = specialise(&examples.neg, &hypotheses, &heap, predicate_table, config);

    let surviving_count = retained.iter().filter(|&&b| b).count();
    let rejected_count = hypotheses.len() - surviving_count;
    println!(
        "\n=== Specialisation Results ===\n{} hypotheses survived, {} rejected",
        surviving_count, rejected_count
    );

    // Build final top program: union all surviving clauses, deduplicated
    let mut seen = HashSet::new();
    let mut top_program: Vec<&Clause> = Vec::new();
    for (hypothesis, &alive) in hypotheses.iter().zip(retained.iter()) {
        if alive {
            for clause in hypothesis {
                let key = clause.to_string(&heap);
                if seen.insert(key) {
                    top_program.push(clause);
                }
            }
        }
    }

    println!("\n=== Top Program ({} clauses) ===", top_program.len());
    for clause in &top_program {
        println!("  {}", clause.to_string(&heap));
    }

    // TODO: Step 3 — Reduce

    ExitCode::SUCCESS
}

/// Parse a single example string into a goal on the given query heap.
fn parse_example(example: &str, query_heap: &mut QueryHeap) -> Result<usize, String> {
    let query = format!(":-{example}.");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Example '{example}' incorrectly formatted")),
    };
    let clause = build_clause(literals, None, None, query_heap, true);
    Ok(clause[0])
}

/// Minimal work on the worker thread — just the copy.
fn extract_hypothesis_local(proof: &Proof) -> (Vec<Cell>, Vec<Clause>) {
    let mut local_cells: Vec<Cell> = Vec::new();
    let mut ref_map = HashMap::new();
    let mut clauses = Vec::new();

    for clause in proof.hypothesis.iter() {
        let new_literals: Vec<usize> = clause
            .iter()
            .map(|&lit_addr| {
                local_cells.copy_term_with_ref_map(&proof.heap, lit_addr, &mut ref_map)
            })
            .collect();
        clauses.push(Clause::new(new_literals, None, None));
    }

    (local_cells, clauses)
}

fn generalise(
    pos_examples: &[String],
    predicate_table: &PredicateTable,
    heap: &[Cell],
    config: Config,
) -> (Vec<Cell>,Vec<Vec<Clause>>){
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT - 1)
        .build()
        .unwrap();

    let (tx, rx) = mpsc::channel::<HypothesisMsg>();
    let total = pos_examples.len();
    let completed = Arc::new(AtomicUsize::new(0));
    let heap_len = heap.len();

    // Collector runs on its own OS thread, processing results as they arrive
    let collector = thread::spawn(move || {
        let mut hypothesis_cells = Vec::new();
        let mut hypotheses = Vec::new();
        let mut seen = HashSet::new();
        let mut offset = heap_len;

        for HypothesisMsg { cells, mut h } in rx {
            // Build canonical key before offset adjustment, using local cells
            let mut clause_strings: Vec<String> =
                h.iter().map(|clause| clause.to_string(&cells)).collect();
            clause_strings.sort_unstable();
            let key = clause_strings.join("|");

            if !seen.insert(key) {
                continue; // Duplicate hypothesis, skip
            }

            let len = cells.len();
            for cell in cells {
                let adjusted = match cell {
                    (Tag::Str, addr) => (Tag::Str, addr + offset),
                    (Tag::Lis, addr) => (Tag::Lis, addr + offset),
                    (Tag::Ref, addr) => (Tag::Ref, addr + offset),
                    other => other,
                };
                hypothesis_cells.push(adjusted);
            }
            for clause in h.iter_mut() {
                for literal in clause.iter_mut() {
                    *literal += offset;
                }
            }
            hypotheses.push(h);
            offset += len;
        }

        (hypothesis_cells, hypotheses)
    });

    // Workers — scope blocks until all are done, then drops tx clones
    pool.scope(|s| {
        for example in pos_examples {
            let tx = tx.clone();
            let completed = completed.clone();
            s.spawn(move |_| {
                generalise_thread(example, predicate_table, &heap, config, tx);
                let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
                eprint!("\rGeneralise: {done}/{total} examples");
                let _ = io::stderr().flush();
            });
        }
    });
    drop(tx); // drop the original sender so the collector's rx iterator ends
    eprintln!(" ...done");

    collector.join().unwrap()
}

fn generalise_thread(
    example: &str,
    predicate_table: &PredicateTable,
    prog_heap: &[Cell],
    config: Config,
    tx: Sender<HypothesisMsg>,
) {
    let mut query_heap = QueryHeap::new(prog_heap, None);
    let goal = match parse_example(&example, &mut query_heap) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Failed to parse example '{}': {}", example, e);
            return;
        }
    };
    let mut proof = Proof::new(query_heap, &[goal]);

    while proof.prove(predicate_table, config) {
        for clause in proof.hypothesis.iter() {
            clause.normalise_clause_vars(&mut proof.heap);
            let (cells, h) = extract_hypothesis_local(&proof);
            if tx.send(HypothesisMsg { cells, h }).is_err() {
                break; // Receiver dropped
            }
        }
    }
}

fn specialise(
    neg_examples: &[String],
    hypotheses: &[Vec<Clause>],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> Vec<bool> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT - 1)
        .build()
        .unwrap();

    let (tx, rx) = mpsc::channel::<(usize, bool)>();
    let total = hypotheses.len();
    let completed = Arc::new(AtomicUsize::new(0));

    // Collector: build the retain mask as results arrive
    let collector = thread::spawn(move || {
        let mut retained = vec![true; total];
        for (idx, keep) in rx {
            retained[idx] = keep;
        }
        retained
    });

    // One worker per hypothesis
    pool.scope(|s| {
        for (idx, hypothesis) in hypotheses.iter().enumerate() {
            let tx = tx.clone();
            let completed = completed.clone();
            s.spawn(move |_| {
                let keep = specialise_thread(neg_examples, hypothesis, heap, predicate_table, config);
                let _ = tx.send((idx, keep));
                let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
                eprint!("\rSpecialise: {done}/{total} hypotheses tested");
                let _ = io::stderr().flush();
            });
        }
    });
    drop(tx);
    eprintln!(" ...done");

    collector.join().unwrap()
}

/// Test one hypothesis against all negative examples.
/// Returns `true` if the hypothesis should be retained (no negative is provable).
fn specialise_thread(
    neg_examples: &[String],
    hypothesis: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    // Use the original max_depth to bound recursive hypotheses, but disable learning
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
    };

    // Build a Hypothesis from the clauses so we can use Proof::with_hypothesis
    let mut h = Hypothesis::new();
    for clause in hypothesis {
        h.push_clause(clause.clone(), SmallVec::new());
    }

    for example in neg_examples {
        let mut query_heap = QueryHeap::new(heap, None);
        let goal = match parse_example(example, &mut query_heap) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Failed to parse negative example '{}': {}", example, e);
                continue;
            }
        };
        let mut proof = Proof::with_hypothesis(query_heap, &[goal], h);
        // If any negative example is provable, reject this hypothesis
        if proof.prove(predicate_table, config) {
            return false;
        }
        // Reclaim the hypothesis — it was never mutated since max_clause is 0
        h = std::mem::replace(&mut proof.hypothesis, Hypothesis::new());
    }
    true
}