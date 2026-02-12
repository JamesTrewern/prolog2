use std::{
    collections::{HashMap, HashSet},
    process::ExitCode,
    sync::{mpsc, Arc},
    thread,
};

use crate::{
    Config, Examples,
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
    },
    parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::build_clause,
        tokeniser::tokenise,
    },
    program::{clause::Clause, hypothesis::{Constraints, Hypothesis}, predicate_table::PredicateTable},
    resolution::proof::Proof,
};

/// Message sent from a proof thread to the main thread.
struct HypothesisMsg {
    cells: Vec<Cell>,
    clauses: Vec<Clause>,
}

/// Accumulated Top Program: a heap of cells and unique hypotheses.
struct TopProgramAccumulator {
    cells: Vec<Cell>,
    hypotheses: Vec<Vec<Clause>>,
    seen: HashSet<String>,
}

impl TopProgramAccumulator {
    fn new() -> Self {
        TopProgramAccumulator {
            cells: Vec::new(),
            hypotheses: Vec::new(),
            seen: HashSet::new(),
        }
    }

    /// Normalise Ref addresses in local cells to sequential 0,1,2...
    /// by first-appearance order across clause literals (sorted).
    /// Mutates cells in place and returns a mapping for display/key purposes.
    fn normalise_refs(cells: &mut Vec<Cell>, clauses: &[Clause]) {
        // Collect unique Ref addresses in first-appearance order
        let mut ref_addrs: Vec<usize> = Vec::new();
        for clause in clauses {
            for &lit_addr in clause.iter() {
                Self::collect_refs(cells, lit_addr, &mut ref_addrs);
            }
        }

        // Build old_addr -> new_index mapping (for future use)
        let _remap: HashMap<usize, usize> = ref_addrs
            .iter()
            .enumerate()
            .map(|(new_idx, &old_addr)| (old_addr, new_idx))
            .collect();

        // Rewrite all Ref cells: self-referencing Refs get new sequential addresses,
        // and any cell pointing to a Ref gets updated too.
        // We use a two-pass approach: first allocate new positions, then rewrite.
        // Since Refs are self-referencing, we just need to update their value
        // and any other cell that references them.

        // For now, we just need the normalised variable names for key generation.
        // The actual cells keep their original addresses (they work fine for
        // term_string display via Ref_N). The normalisation is used for the key.
    }

    /// Recursively collect Ref addresses in a term, in first-appearance order.
    fn collect_refs(cells: &[Cell], addr: usize, refs: &mut Vec<usize>) {
        // Simple deref
        let mut a = addr;
        loop {
            match cells[a] {
                (Tag::Ref, ptr) if ptr == a => {
                    if !refs.contains(&a) {
                        refs.push(a);
                    }
                    return;
                }
                (Tag::Ref, ptr) => a = ptr,
                _ => break,
            }
        }
        match cells[a] {
            (Tag::Str, ptr) => Self::collect_refs(cells, ptr, refs),
            (Tag::Func | Tag::Tup | Tag::Set, length) => {
                for i in 1..=length {
                    Self::collect_refs(cells, a + i, refs);
                }
            }
            (Tag::Lis, ptr) => {
                Self::collect_refs(cells, ptr, refs);
                Self::collect_refs(cells, ptr + 1, refs);
            }
            _ => {}
        }
    }

    /// Generate a canonical key from local cells.
    /// Clause strings are sorted; variable names are normalised to V0,V1,...
    fn canonical_key(cells: &[Cell], clauses: &[Clause]) -> String {
        // Collect refs in order for normalised naming
        let mut ref_addrs: Vec<usize> = Vec::new();
        for clause in clauses {
            for &lit_addr in clause.iter() {
                Self::collect_refs(cells, lit_addr, &mut ref_addrs);
            }
        }
        let remap: HashMap<usize, usize> = ref_addrs
            .iter()
            .enumerate()
            .map(|(i, &addr)| (addr, i))
            .collect();

        // Build clause strings with normalised var names
        let mut clause_strings: Vec<String> = clauses
            .iter()
            .map(|clause| {
                let mut buf = String::new();
                for (j, &lit_addr) in clause.iter().enumerate() {
                    if j == 1 { buf.push_str(":-"); }
                    else if j > 1 { buf.push(','); }
                    Self::term_string_normalised(cells, lit_addr, &remap, &mut buf);
                }
                buf.push('.');
                buf
            })
            .collect();
        clause_strings.sort();
        clause_strings.join("|")
    }

    /// Write a normalised term string where Ref_N is replaced with V<index>.
    fn term_string_normalised(
        cells: &[Cell],
        addr: usize,
        remap: &HashMap<usize, usize>,
        buf: &mut String,
    ) {
        // Deref
        let mut a = addr;
        loop {
            match cells[a] {
                (Tag::Ref, ptr) if ptr == a => break,
                (Tag::Ref, ptr) => a = ptr,
                _ => break,
            }
        }

        use std::fmt::Write;
        use crate::heap::heap::EMPTY_LIS;
        use crate::heap::symbol_db::SymbolDB;

        match cells[a] {
            (Tag::Ref, r) if r == a => {
                if let Some(&idx) = remap.get(&a) {
                    write!(buf, "V{}", idx).unwrap();
                } else {
                    write!(buf, "V?{}", a).unwrap();
                }
            }
            (Tag::Con, id) => buf.push_str(&SymbolDB::get_const(id)),
            (Tag::Int, val) => {
                let v: isize = unsafe { std::mem::transmute_copy(&val) };
                write!(buf, "{}", v).unwrap();
            }
            (Tag::Flt, val) => {
                let v: fsize::fsize = unsafe { std::mem::transmute_copy(&val) };
                write!(buf, "{}", v).unwrap();
            }
            EMPTY_LIS => buf.push_str("[]"),
            (Tag::Str, ptr) => Self::term_string_normalised(cells, ptr, remap, buf),
            (Tag::Func | Tag::Tup | Tag::Set, length) => {
                let (open, close) = match cells[a].0 {
                    Tag::Func => ("(", ")"),
                    Tag::Tup => ("(", ")"),
                    Tag::Set => ("{", "}"),
                    _ => unreachable!(),
                };
                // First sub-term is the functor name for Func
                Self::term_string_normalised(cells, a + 1, remap, buf);
                if length > 1 {
                    buf.push_str(open);
                    for i in 2..=length {
                        if i > 2 { buf.push(','); }
                        Self::term_string_normalised(cells, a + i, remap, buf);
                    }
                    buf.push_str(close);
                }
            }
            (Tag::Lis, ptr) => {
                buf.push('[');
                Self::list_string_normalised(cells, ptr, remap, buf);
                buf.push(']');
            }
            _ => write!(buf, "?{:?}", cells[a]).unwrap(),
        }
    }

    fn list_string_normalised(
        cells: &[Cell],
        mut ptr: usize,
        remap: &HashMap<usize, usize>,
        buf: &mut String,
    ) {
        loop {
            Self::term_string_normalised(cells, ptr, remap, buf);
            // Deref tail
            let mut tail = ptr + 1;
            loop {
                match cells[tail] {
                    (Tag::Ref, r) if r == tail => break,
                    (Tag::Ref, r) => tail = r,
                    _ => break,
                }
            }
            match cells[tail] {
                (Tag::Lis, next_ptr) => {
                    buf.push(',');
                    ptr = next_ptr;
                }
                (Tag::ELis, _) => break,
                _ => {
                    buf.push('|');
                    Self::term_string_normalised(cells, tail, remap, buf);
                    break;
                }
            }
        }
    }

    /// Process a received hypothesis message: normalise, generate key,
    /// deduplicate, and if new, append to accumulator with offset adjustment.
    fn receive(&mut self, msg: HypothesisMsg) -> bool {
        let cells = msg.cells;
        let clauses = msg.clauses;

        // Sort clauses by normalised string for canonical ordering
        // First generate key with clauses in sorted order
        let key = Self::canonical_key(&cells, &clauses);

        if !self.seen.insert(key) {
            return false;
        }

        let offset = self.cells.len();

        for cell in &cells {
            let adjusted = match cell {
                (Tag::Str, addr) => (Tag::Str, addr + offset),
                (Tag::Lis, addr) => (Tag::Lis, addr + offset),
                (Tag::Ref, addr) => (Tag::Ref, addr + offset),
                other => *other,
            };
            self.cells.push(adjusted);
        }

        let clauses = clauses
            .into_iter()
            .map(|clause| {
                let new_lits: Vec<usize> = clause
                    .iter()
                    .map(|&addr| addr + offset)
                    .collect();
                Clause::new(new_lits, None)
            })
            .collect();

        self.hypotheses.push(clauses);
        true
    }
}

/// Specialise: test each hypothesis against negative examples.
/// Returns a Box<[bool]> where true means the hypothesis survived
/// (did not entail any negative example).
fn specialise(
    accumulator: &TopProgramAccumulator,
    neg_examples: &[String],
    predicate_table: &Arc<PredicateTable>,
    original_heap: &Arc<Vec<Cell>>,
    config: Config,
) -> Box<[bool]> {
    if neg_examples.is_empty() {
        // No negatives — all hypotheses survive
        return vec![true; accumulator.hypotheses.len()].into_boxed_slice();
    }

    // Build extended prog_cells: original + accumulated
    let mut extended_cells = (**original_heap).clone();
    let offset = extended_cells.len();
    for cell in &accumulator.cells {
        let adjusted = match cell {
            (Tag::Str, addr) => (Tag::Str, addr + offset),
            (Tag::Lis, addr) => (Tag::Lis, addr + offset),
            (Tag::Ref, addr) => (Tag::Ref, addr + offset),
            other => *other,
        };
        extended_cells.push(adjusted);
    }
    let extended_heap = Arc::new(extended_cells);

    // Config for specialise: no new clauses or predicates
    let spec_config = Config {
        max_clause: 0,
        max_pred: 0,
        ..config
    };

    let handles: Vec<_> = accumulator
        .hypotheses
        .iter()
        .enumerate()
        .map(|(i, hyp_clauses)| {
            let extended_heap = extended_heap.clone();
            let predicate_table = predicate_table.clone();
            let neg_examples: Vec<String> = neg_examples.to_vec();

            // Build Hypothesis with offset-adjusted clause addresses
            let mut hypothesis = Hypothesis::new();
            let empty_constraints: Constraints = Arc::from(Vec::<usize>::new().into_boxed_slice());
            for clause in hyp_clauses {
                let adjusted_lits: Vec<usize> = clause
                    .iter()
                    .map(|&addr| addr + offset)
                    .collect();
                let adjusted_clause = Clause::new(adjusted_lits, None);
                hypothesis.push_clause(adjusted_clause, empty_constraints.clone());
            }

            thread::spawn(move || {
                for neg_example in &neg_examples {
                    let mut query_heap = QueryHeap::new(extended_heap.clone(), None);
                    let goal = match parse_example(neg_example, &mut query_heap) {
                        Ok(g) => g,
                        Err(e) => {
                            eprintln!("Failed to parse negative example '{}': {}", neg_example, e);
                            continue;
                        }
                    };

                    let mut proof = Proof::with_hypothesis(
                        query_heap,
                        &[goal],
                        hypothesis.clone(),
                    );

                    if proof.prove(predicate_table.clone(), spec_config) {
                        // Hypothesis entails a negative example — reject it
                        if config.debug {
                            eprintln!(
                                "[SPECIALISE] Hypothesis {} entails negative '{}' — rejected",
                                i, neg_example
                            );
                        }
                        return false;
                    }
                }
                // Survived all negative examples
                true
            })
        })
        .collect();

    let results: Vec<bool> = handles
        .into_iter()
        .map(|h| h.join().expect("Specialise thread panicked"))
        .collect();

    results.into_boxed_slice()
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
                local_cells.copy_term_with_ref_map(
                    &proof.heap,
                    lit_addr,
                    &mut ref_map,
                )
            })
            .collect();
        clauses.push(Clause::new(new_literals, None));
    }

    (local_cells, clauses)
}

/// Parse a single example string into a goal on the given query heap.
fn parse_example(example: &str, query_heap: &mut QueryHeap) -> Result<usize, String> {
    let query = format!(":-{example}.");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Example '{example}' incorrectly formatted")),
    };
    let clause = build_clause(literals, None, query_heap, true);
    Ok(clause[0])
}

/// Generalise: spawn a proof thread per positive example, each sending
/// hypotheses over a channel. Main thread receives, normalises, and deduplicates.
fn generalise(
    pos_examples: &[String],
    predicate_table: &Arc<PredicateTable>,
    heap: &Arc<Vec<Cell>>,
    config: Config,
) -> TopProgramAccumulator {
    let (tx, rx) = mpsc::channel::<HypothesisMsg>();

    let handles: Vec<_> = pos_examples
        .iter()
        .enumerate()
        .map(|(i, example)| {
            let example = example.clone();
            let predicate_table = predicate_table.clone();
            let heap = heap.clone();
            let tx = tx.clone();

            thread::spawn(move || {
                let mut query_heap = QueryHeap::new(heap, None);
                let goal = match parse_example(&example, &mut query_heap) {
                    Ok(g) => g,
                    Err(e) => {
                        eprintln!("Failed to parse example '{}': {}", example, e);
                        return;
                    }
                };

                let mut proof = Proof::new(query_heap, &[goal]);
                let mut solution_count: usize = 0;

                while proof.prove(predicate_table.clone(), config) {
                    solution_count += 1;
                    let (cells, clauses) = extract_hypothesis_local(&proof);
                    let _ = tx.send(HypothesisMsg { cells, clauses });
                }

                println!(
                    "  Example {} '{}': {} solutions",
                    i + 1, example, solution_count
                );
            })
        })
        .collect();

    drop(tx);

    // Main thread: receive, normalise, deduplicate
    let mut accumulator = TopProgramAccumulator::new();
    let mut total = 0usize;
    for msg in rx {
        total += 1;
        accumulator.receive(msg);
    }

    for handle in handles {
        handle.join().expect("Proof thread panicked");
    }

    println!(
        "  Total: {} solutions, {} unique",
        total,
        accumulator.hypotheses.len()
    );

    accumulator
}

/// Top Program Construction entry point
pub fn run(
    examples: Examples,
    predicate_table: Arc<PredicateTable>,
    heap: Arc<Vec<Cell>>,
    config: Config,
) -> ExitCode {
    println!("=== Top Program Construction ===");
    println!(
        "Positive examples: {}, Negative examples: {}",
        examples.pos.len(),
        examples.neg.len()
    );

    let accumulator = generalise(&examples.pos, &predicate_table, &heap, config);

    println!("\n=== Generalisation Results ===");
    println!(
        "{} unique hypotheses, {} heap cells",
        accumulator.hypotheses.len(),
        accumulator.cells.len()
    );

    for (i, hypothesis) in accumulator.hypotheses.iter().enumerate() {
        println!("Hypothesis [{}]:", i);
        for clause in hypothesis {
            println!("  {}", clause.to_string(&accumulator.cells));
        }
    }

    // Step 2: Specialise
    let survived = specialise(&accumulator, &examples.neg, &predicate_table, &heap, config);

    let surviving_count = survived.iter().filter(|&&b| b).count();
    let rejected_count = accumulator.hypotheses.len() - surviving_count;
    println!("\n=== Specialisation Results ===");
    println!(
        "{} hypotheses survived, {} rejected",
        surviving_count, rejected_count
    );

    // Build final top program from surviving hypotheses
    println!("\n=== Top Program ===");
    for (i, (hypothesis, &alive)) in accumulator.hypotheses.iter().zip(survived.iter()).enumerate() {
        if alive {
            println!("Hypothesis [{}]:", i);
            for clause in hypothesis {
                println!("  {}", clause.to_string(&accumulator.cells));
            }
        }
    }

    // Step 3: Reduce (TODO)

    ExitCode::SUCCESS
}
