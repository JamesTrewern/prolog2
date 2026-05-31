use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, Sender},
        Arc,
    },
    thread, usize,
};

use crate::{
    app::{App, TopProg},
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
    },
    parser::{build_tree::TokenStream, execute_tree::build_clause, tokeniser::tokenise},
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::proof::Proof,
    Config,
};

use lazy_static::lazy_static;
use rayon;
use smallvec::SmallVec;



lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

pub enum TopProgError {}

/// Message sent from a proof thread to the main thread.
struct HypothesisMsg {
    cells: Vec<Cell>,
    h: Vec<Clause>,
}

impl App {
    pub fn run_top_prog(&mut self) -> String{
        let Some(mut examples) = self.examples.clone() else {
            panic!("Can't start top prog without examples");
        };
        let reduce = match self.top_prog {
            TopProg::True(reduce) => reduce,
            _ => false,
        };
        println!("=== Top Program Construction ===");
        println!(
            "Positive examples: {}, Negative examples: {}",
            examples.pos.len(),
            examples.neg.len()
        );
        examples.normalise_for_top_prog();

        let (cells, mut sub_hypotheses) = generalise(
            &examples.pos,
            &self.predicate_table,
            &self.prog_heap,
            self.config,
        );

        self.prog_heap.extend_from_slice(&cells);

        println!(
            "\n=== Generalisation Results ===\n{} unique hypotheses",
            sub_hypotheses.len(),
        );

        // Step 2: Specialise
        let retained = specialise(
            &examples.neg,
            &sub_hypotheses,
            &self.prog_heap,
            &self.predicate_table,
            self.config,
        );

        let surviving_count = retained.iter().filter(|&&b| b).count();
        let rejected_count = sub_hypotheses.len() - surviving_count;
        println!(
            "\n=== Specialisation Results ===\n{} hypotheses survived, {} rejected",
            surviving_count, rejected_count
        );

        sub_hypotheses = sub_hypotheses
            .into_iter()
            .zip(retained.iter())
            .filter_map(|(h, &alive)| if alive { Some(h) } else { None })
            .collect();

        // Build final top program from surviving hypotheses
        if reduce {
            let reduced = reduce_hypotheses(
                &examples.pos,
                sub_hypotheses,
                &self.prog_heap,
                &self.predicate_table,
                self.config,
            );
            println!("\n=== Reduced Program ({} clauses) ===", reduced.len());
            let mut buffer = String::new();
            for clause in &reduced {
                buffer += &format!("{}\n", clause.to_string(&self.prog_heap));
            }
            println!("{buffer}");
            buffer
        } else {
            let top_program = union_sub_hypotheses_renumbered(sub_hypotheses, &self.prog_heap);
            println!("\n=== Top Program ({} clauses) ===", top_program.len());
            let mut buffer = String::new();
            for clause in &top_program {
                buffer += &format!("{clause}\n");
            }
            println!("{buffer}");
            buffer
        }
    }
}

/// Parse a single example string into a goal on the given query heap.
fn parse_example(example: &str, query_heap: &mut QueryHeap) -> Result<usize, String> {
    let literals = TokenStream::new(tokenise(example).map_err(|e| e.to_string())?)
        .parse_goals()
        .map_err(|e| format!("Example '{example}' incorrectly formatted: {e}"))?;
    let clause = build_clause(literals, None, None, query_heap, true);
    Ok(clause[0])
}

/// Minimal work on the worker thread — just the copy.
fn extract_hypothesis_local(proof: &Proof, heap: &impl Heap) -> (Vec<Cell>, Vec<Clause>) {
    let mut local_cells: Vec<Cell> = Vec::new();
    let mut ref_map = HashMap::new();
    let mut clauses = Vec::new();

    for clause in proof.hypothesis.iter() {
        let new_literals: Vec<usize> = clause
            .iter()
            .map(|&lit_addr| local_cells.copy_term(heap, lit_addr, &mut ref_map))
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
            // Build canonical key before offset adjustment, using local cells.
            // Normalise invented predicate names so that structurally identical
            // hypotheses (differing only in pred_N numbering) are deduplicated.
            let clause_strings: Vec<String> =
                h.iter().map(|clause| clause.to_string(&cells)).collect();
            let key = crate::hypothesis_canonical_key(&clause_strings);

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
    let mut proof = Proof::new(&query_heap, &[goal]);

    while proof.prove(&mut query_heap, predicate_table, config) {
        for clause in proof.hypothesis.iter() {
            clause.normalise_clause_vars(&mut query_heap);
            let (cells, h) = extract_hypothesis_local(&proof, &query_heap);
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
        let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h);
        // If any negative example is provable, reject this hypothesis
        if proof.prove(&mut query_heap, predicate_table, config) {
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
    clauses: &[Clause],
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
            let mut proof = Proof::with_hypothesis(&query_heap, &[goal], h.clone());
            proof.prove(&mut query_heap, predicate_table, config)
        })
        .count()
}

fn reduce_hypotheses(
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
        let coverage = count_coverage(pos_examples, &reduced, &heap, predicate_table, config);
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
fn reduce<'a>(
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
    };

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

fn union_sub_hypotheses(sub_hypotheses: Vec<Vec<Clause>>, heap: &Vec<Cell>) -> Vec<Clause> {
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

/// String-based union that deduplicates invented predicates across hypotheses.
///
/// For each hypothesis, invented predicates are processed bottom-up (leaves
/// first). Each predicate's definition — with callees already resolved to
/// their canonical union names — is checked against a global registry. If an
/// identical definition already exists, the predicate is mapped to the
/// existing name. Otherwise it gets a fresh global name and its clauses are
/// added to the union.
fn union_sub_hypotheses_renumbered(
    sub_hypotheses: Vec<Vec<Clause>>,
    heap: &Vec<Cell>,
) -> Vec<String> {
    // Registry: skeleton key → global pred name
    let mut registry: HashMap<String, String> = HashMap::new();
    let mut top_program: Vec<String> = Vec::new();
    let mut global_counter = 1usize;
    // Also dedup non-invented clauses (e.g. in_cluster bridge clauses)
    let mut seen_clauses: HashSet<String> = HashSet::new();

    for hypothesis in sub_hypotheses {
        // Convert to strings, normalise within hypothesis
        let clause_strings: Vec<String> = hypothesis
            .iter()
            .map(|c| c.to_string(heap))
            .collect();
        let normalised = crate::normalise_hypothesis(&clause_strings);

        // Group clauses by head predicate name
        let mut pred_clauses: HashMap<String, Vec<String>> = HashMap::new();
        let mut non_invented: Vec<String> = Vec::new();

        for clause in &normalised {
            let head_name = clause.split('(').next().unwrap_or("");
            if head_name.starts_with("pred_") {
                pred_clauses
                    .entry(head_name.to_string())
                    .or_default()
                    .push(clause.clone());
            } else {
                non_invented.push(clause.clone());
            }
        }

        // Build dependency graph: which invented preds does each one call?
        let pred_names: Vec<String> = pred_clauses.keys().cloned().collect();
        let mut deps: HashMap<String, Vec<String>> = HashMap::new();
        for (pred_name, clauses) in &pred_clauses {
            let mut callees = Vec::new();
            for clause in clauses {
                for token in crate::find_pred_tokens(clause) {
                    if token != *pred_name
                        && pred_names.contains(&token)
                        && !callees.contains(&token)
                    {
                        callees.push(token);
                    }
                }
            }
            deps.insert(pred_name.clone(), callees);
        }

        // Topological sort: leaves first (preds with no invented-pred dependencies)
        let topo_order = topo_sort(&pred_names, &deps);

        // Process each predicate in bottom-up order
        // Maps local normalised name → global union name
        let mut local_to_global: HashMap<String, String> = HashMap::new();

        for pred_name in &topo_order {
            let clauses = match pred_clauses.get(pred_name) {
                Some(c) => c,
                None => continue,
            };

            // Apply already-resolved mappings to callee names in these clauses
            let resolved_clauses: Vec<String> = clauses
                .iter()
                .map(|c| apply_mapping(c, &local_to_global))
                .collect();

            // Build skeleton: replace THIS pred's name with "$HEAD",
            // normalise variable names, sort clauses
            let mut skeleton_clauses: Vec<String> = resolved_clauses
                .iter()
                .map(|c| {
                    let replaced = c.replace(pred_name.as_str(), "$HEAD");
                    normalise_vars(&replaced)
                })
                .collect();
            skeleton_clauses.sort();
            let skeleton_key = skeleton_clauses.join("|");

            if let Some(existing_name) = registry.get(&skeleton_key) {
                // This predicate already exists in the union — reuse it
                local_to_global.insert(pred_name.clone(), existing_name.clone());
            } else {
                // New predicate — assign global name, add clauses
                let global_name = format!("pred_{global_counter}");
                global_counter += 1;

                registry.insert(skeleton_key, global_name.clone());
                local_to_global.insert(pred_name.clone(), global_name.clone());

                // Add clauses with the global name
                for clause in &resolved_clauses {
                    let final_clause = clause.replace(pred_name.as_str(), global_name.as_str());
                    if seen_clauses.insert(final_clause.clone()) {
                        top_program.push(final_clause);
                    }
                }
            }
        }

        // Add non-invented clauses (e.g. in_cluster bridge), applying mappings
        for clause in &non_invented {
            let final_clause = apply_mapping(clause, &local_to_global);
            if seen_clauses.insert(final_clause.clone()) {
                top_program.push(final_clause);
            }
        }
    }

    top_program
}

/// Normalise variable names in a clause string by replacing each `Arg_N` with
/// `V0`, `V1`, … in order of first appearance.
fn normalise_vars(clause: &str) -> String {
    let mut result = String::with_capacity(clause.len());
    let bytes = clause.as_bytes();
    let mut var_map: Vec<(String, String)> = Vec::new();
    let mut counter = 0usize;
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i..].starts_with(b"Arg_") {
            let start = i;
            i += 4; // skip "Arg_"
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let var_name = &clause[start..i];
            let canonical = if let Some((_, canon)) = var_map.iter().find(|(orig, _)| orig == var_name) {
                canon.clone()
            } else {
                let canon = format!("V{counter}");
                counter += 1;
                var_map.push((var_name.to_string(), canon.clone()));
                canon
            };
            result.push_str(&canonical);
        } else {
            result.push(bytes[i] as char);
            i += 1;
        }
    }
    result
}

/// Apply a pred-name mapping to a clause string, replacing longest names first
/// to avoid partial matches (e.g. "pred_10" before "pred_1").
fn apply_mapping(clause: &str, mapping: &HashMap<String, String>) -> String {
    if mapping.is_empty() {
        return clause.to_string();
    }
    let mut pairs: Vec<(&str, &str)> = mapping.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();
    pairs.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    let mut result = clause.to_string();
    for (old, new) in pairs {
        result = result.replace(old, new);
    }
    result
}

/// Topological sort: returns leaves first (predicates with no invented-pred
/// dependencies), then predicates that depend on those, etc.
/// Falls back to including remaining nodes if cycles are detected.
fn topo_sort(nodes: &[String], deps: &HashMap<String, Vec<String>>) -> Vec<String> {
    // in_degree counts how many invented predicates this node depends on
    // (i.e. how many callees it has). Leaves have in_degree 0.
    let mut in_degree: HashMap<&str, usize> = HashMap::new();
    // reverse_deps: callee → list of callers
    let mut reverse_deps: HashMap<&str, Vec<&str>> = HashMap::new();

    for node in nodes {
        let callees = deps.get(node).map(|v| v.as_slice()).unwrap_or(&[]);
        let count = callees.iter().filter(|c| nodes.contains(c)).count();
        in_degree.insert(node.as_str(), count);
        for callee in callees {
            if nodes.contains(callee) {
                reverse_deps
                    .entry(callee.as_str())
                    .or_default()
                    .push(node.as_str());
            }
        }
    }

    // Start with leaves (nodes that call no other invented predicates)
    let mut queue: Vec<&str> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(&name, _)| name)
        .collect();
    queue.sort(); // deterministic order

    let mut result = Vec::new();
    while let Some(node) = queue.pop() {
        result.push(node.to_string());
        // For each caller of this node, decrement their in-degree
        if let Some(callers) = reverse_deps.get(node) {
            for &caller in callers {
                if let Some(deg) = in_degree.get_mut(caller) {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        queue.push(caller);
                        queue.sort();
                    }
                }
            }
        }
    }

    // Add any remaining nodes (cycles) at the end
    for node in nodes {
        if !result.contains(node) {
            result.push(node.clone());
        }
    }

    result
}
