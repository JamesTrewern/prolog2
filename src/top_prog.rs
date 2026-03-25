use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    process::ExitCode,
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, Sender},
        Arc,
    },
    thread, usize,
};

use lazy_static::lazy_static;
use rayon;
use smallvec::SmallVec;

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
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::proof::Proof,
    Config, Examples,
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
    examples: &Examples,
    predicate_table: &PredicateTable,
    mut heap: Vec<Cell>,
    config: Config,
    no_reduce: bool,
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

    // Build final top program from surviving hypotheses
    let mut seen = HashSet::new();
    let mut top_program: Vec<&Clause> = Vec::new();

    if no_reduce {
        // Simple union without reduction
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
    } else {
        // Step 2b: Per-hypothesis reduction — remove redundant clauses within each
        // sub-hypothesis before union, so specific clauses don't drown out general ones.
        let surviving: Vec<&Vec<Clause>> = hypotheses
            .iter()
            .zip(retained.iter())
            .filter_map(|(h, &alive)| if alive { Some(h) } else { None })
            .collect();
        let sub_total = surviving.len();

        // Reduce each sub-hypothesis and score by coverage (number of positives entailed)
        let mut scored: Vec<(usize, Vec<&Clause>)> = Vec::new();
        for (idx, hypothesis) in surviving.iter().enumerate() {
            eprint!("\rSub-reduce: {}/{sub_total}    ", idx + 1);
            let _ = io::stderr().flush();
            let clauses: Vec<&Clause> = hypothesis.iter().collect();
            let reduced = reduce(
                &examples.pos,
                clauses,
                &heap,
                predicate_table,
                config,
                false,
            );
            let coverage = count_coverage(&examples.pos, &reduced, &heap, predicate_table, config);
            scored.push((coverage, reduced));
        }
        eprintln!("\rSub-reduce: {sub_total}/{sub_total} ...done    ");

        // Sort by coverage ascending — specific hypotheses first in the union.
        // Plotkin's reduction checks clauses front-to-back: specific clauses get
        // checked first and removed (the general ones behind them cover the same
        // examples). By the time we reach the general clauses, the specific ones
        // are gone and the general ones become essential.
        scored.sort_by(|a, b| a.0.cmp(&b.0));

        // Union all reduced sub-hypothesis clauses, deduplicated
        for (_coverage, reduced_h) in &scored {
            for &clause in reduced_h {
                let key = clause.to_string(&heap);
                if seen.insert(key) {
                    top_program.push(clause);
                }
            }
        }

        println!("\n=== Top Program ({} clauses) ===", top_program.len());
        for clause in &top_program {
            println!("  {}", clause.to_string(&heap));
        }

        // Step 3: Final reduction on the union
        let reduced = reduce(
            &examples.pos,
            top_program,
            &heap,
            predicate_table,
            config,
            true,
        );

        println!("\n=== Reduced Program ({} clauses) ===", reduced.len());
        for clause in &reduced {
            println!("  {}", clause.to_string(&heap));
        }
    }

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
) -> (Vec<Cell>, Vec<Vec<Clause>>) {
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
                let keep =
                    specialise_thread(neg_examples, hypothesis, heap, predicate_table, config);
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

/// Count how many positive examples a set of clauses can prove.
fn count_coverage(
    pos_examples: &[String],
    clauses: &[&Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> usize {
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
    };

    let mut h = Hypothesis::new();
    for clause in clauses {
        h.push_clause((*clause).clone(), SmallVec::new());
    }

    pos_examples
        .iter()
        .filter(|example| {
            let mut query_heap = QueryHeap::new(heap, None);
            let goal = match parse_example(example, &mut query_heap) {
                Ok(g) => g,
                Err(_) => return false,
            };
            let mut proof = Proof::with_hypothesis(query_heap, &[goal], h.clone());
            proof.prove(predicate_table, config)
        })
        .count()
}

/// Plotkin's program reduction (Algorithm 3).
/// Sequentially tries removing each clause; if all positives are still provable
/// without it, the clause is redundant and permanently removed.
fn reduce<'a>(
    pos_examples: &[String],
    mut top_program: Vec<&'a Clause>,
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
    verbose: bool,
) -> Vec<&'a Clause> {
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        max_pred: 0,
        debug: false,
    };

    let total = top_program.len();
    let mut removed = 0usize;
    let mut i = 0;
    while i < top_program.len() {
        if verbose {
            eprint!(
                "\rReduce: {}/{total} checked, {removed} removed    ",
                i + removed + 1
            );
            let _ = io::stderr().flush();
        }

        // Build hypothesis from all clauses except the one at index i
        let mut h = Hypothesis::new();
        for (j, clause) in top_program.iter().enumerate() {
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
            let mut proof = Proof::with_hypothesis(query_heap, &[goal], h.clone());
            proof.prove(predicate_table, config)
        });

        if redundant {
            top_program.remove(i);
            removed += 1;
            // Don't increment i — next clause slides into this position
        } else {
            i += 1;
        }
    }
    if verbose {
        eprintln!(" ...done");
    }

    top_program
}
