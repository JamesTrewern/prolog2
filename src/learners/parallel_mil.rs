use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
        Arc,
    },
    thread, usize,
};

use crate::{
    app::{App, TopProg},
    heap::{Cell, Heap, QueryHeap, Tag::Ref, TermWalk, VarBind::Addr, VarReg, Walk},
    learners::{
        predicate_unification::{PredDef, PredDefTable},
        utils::parse_example,
    },
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};

use super::{sub_h_unification::least_sub_h, utils::collect_used_pred};

use lazy_static::lazy_static;
use rayon;
use smallvec::SmallVec;

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}
/// Message sent from a proof thread to the main thread.
struct HypothesisMsg {
    cells: Vec<Cell>,
    h: Box<[Clause]>,
    pred_defs: Vec<PredDef>,
}

impl App {
    pub fn run_top_prog(&mut self) -> Option<Vec<String>> {
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

        let (cells, mut sub_hypotheses, mut pdt) = generalise(
            &examples.pos,
            &self.predicate_table,
            &self.prog_heap,
            self.config,
        );

        for (i, cell) in cells.iter().enumerate() {
            if cell.0 == Ref {
                panic!("{cell:?}@{i}\n{:?}", &cells[i - 5..i + 5])
            }
        }

        // TODO consider more effecient method for adding pdt clauses to program
        self.prog_heap.extend_from_slice(&cells);
        for pred_def in pdt.pred_defs {
            for clause in pred_def.clauses {
                let symbol_arity = self.prog_heap.symbol_arity(clause.head());
                self.predicate_table
                    .add_clause_to_predicate(clause, symbol_arity);
            }
        }

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
        let Some(mut top_programs) = least_sub_h(
            &examples.pos,
            &examples.neg,
            sub_hypotheses,
            &self.prog_heap,
            &self.predicate_table,
            self.config.max_depth,
        ) else {
            println!("No Valid Hypothesis Found");
            return None;
        };
        let mut buffer = Vec::new();
        for (i, mut top_program) in top_programs.into_iter().enumerate() {
            println!("Program {i}");
            collect_used_pred(&mut top_program, &self.prog_heap, &self.predicate_table);
            buffer.push(top_prog_to_string(top_program, &self.prog_heap));
        }
        Some(buffer)
    }
}

fn generalise(
    pos_examples: &[String],
    predicate_table: &PredicateTable,
    heap: &[Cell],
    config: Config,
) -> (Vec<Cell>, Vec<Box<[Clause]>>, PredDefTable) {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT - 1)
        .build()
        .unwrap();

    let (tx, rx) = mpsc::channel::<HypothesisMsg>();
    let total = pos_examples.len();
    let completed = Arc::new(AtomicUsize::new(0));

    pool.in_place_scope(|s| {
        for example in pos_examples {
            let tx = tx.clone();
            let completed = completed.clone();
            s.spawn(move |_| {
                generalise_thread(example, predicate_table, heap, config, tx);
                let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
                eprint!("\rGeneralise: {done}/{total} examples");
                let _ = io::stderr().flush();
            });
        }
        drop(tx); // only the workers' clones are left, so rx ends when they finish
        generalise_collector(heap, rx)
    })
}

fn generalise_collector(
    heap: &[Cell],
    rx: Receiver<HypothesisMsg>,
) -> (Vec<Cell>, Vec<Box<[Clause]>>, PredDefTable) {
    let mut seen = HashSet::new();
    let mut hypotheses = Vec::new();
    let mut pdt = PredDefTable::default();
    let mut acc_heap = QueryHeap::new(heap, None);

    acc_heap.var_regs.extend_from_slice(&[VarReg::UNBOUND; 64]);

    let _ = io::stderr().flush();

    for HypothesisMsg {
        mut cells,
        mut h,
        mut pred_defs,
    } in rx
    {
        let heap_point = acc_heap.heap_point();
        // translate hypothesis message to local context
        // update clause literal addresses
        for clause in &mut h {
            for literal in clause.iter_mut() {
                *literal += acc_heap.heap_len()
            }
        }
        for pred_def in &mut pred_defs {
            for clause in &mut pred_def.clauses {
                for literal in clause.iter_mut() {
                    *literal += acc_heap.heap_len()
                }
            }
        }
        acc_heap.cells.append(&mut cells);
        // Unify predicate defintions with table
        for pred_def in pred_defs {
            pdt.insert(pred_def, &mut acc_heap);
        }

        // Create key, if not in seen add to hypotheses accumulator
        let mut clause_strings: Vec<String> = h.iter().map(|c| c.to_string(&acc_heap)).collect();
        clause_strings.sort_by_key(|s| s.len());
        let key = clause_strings.concat();
        // If seen revert to heap point
        if seen.insert(key) {
            // Ground all ref cells to referenced value
            // TODO Attempt to make branchless vectorisable
            for i in (heap_point.0..acc_heap.cells.len()) {
                if let (Ref, var_id) = acc_heap.cells[i] {
                    let Addr(addr) = acc_heap.var_deref(var_id) else {
                        panic!("Not all variable predicates given constant terms")
                    };
                    acc_heap.cells[i] = acc_heap[addr];
                }
            }
            hypotheses.push(h);
        } else {
            acc_heap.truncate(heap_point);
        }
        // After predicate coining no ref cells should be left, set all regs to unbound
        for var_reg in &mut acc_heap.var_regs {
            *var_reg = VarReg::UNBOUND;
        }
    }

    (acc_heap.cells, hypotheses, pdt)
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
        let (cells, mut h) = extract_hypothesis_local(&proof, &query_heap);
        let pred_defs = PredDef::extract_pred_defs_from_h(&mut h, &cells);
        if tx
            .send(HypothesisMsg {
                cells: cells.cells,
                h: h.into_boxed_slice(),
                pred_defs,
            })
            .is_err()
        {
            break; // Receiver dropped
        }
    }
}

/// Extract cells and remap literal addrs from hypothesis
fn extract_hypothesis_local(proof: &Proof, heap: &QueryHeap) -> (QueryHeap<'static>, Vec<Clause>) {
    let mut local_cells = QueryHeap::new(&[], None);
    let mut clauses = Vec::with_capacity(proof.hypothesis.len());
    let mut ref_map = HashMap::new();
    for clause in proof.hypothesis.iter() {
        let new_literals: Vec<usize> = clause
            .iter()
            .map(|&lit_addr| {
                let addr = local_cells.heap_len();
                local_cells.clone_term_from_other(heap, lit_addr, &mut ref_map);
                addr
            })
            .collect();
        clauses.push(Clause::new(new_literals, None, clause.max_arg_id));
    }

    (local_cells, clauses)
}

fn extract_literal(dst: &mut Vec<Cell>, src: &QueryHeap, addr: usize) -> usize {
    let return_addr = dst.heap_len();
    let mut walk = TermWalk::new(addr);
    while let Some(cell) = walk.next_cell(src) {
        dst.push(cell);
    }
    return_addr
}

fn specialise(
    neg_examples: &[String],
    hypotheses: &[Box<[Clause]>],
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
        protect_h_preds: config.protect_h_preds,
    };

    for example in neg_examples {
        let mut query_heap = QueryHeap::new(heap, None);
        let goal = match parse_example(example, &mut query_heap) {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Failed to parse negative example '{}': {}", example, e);
                continue;
            }
        };
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(&hypothesis);
        // If any negative example is provable, reject this hypothesis
        if proof.prove(&mut query_heap, predicate_table, config) {
            return false;
        }
    }
    true
}

fn top_prog_to_string(top_program: Vec<Clause>, heap: &impl Heap) -> String {
    let mut buffer = String::new();
    for clause in &top_program {
        buffer += &format!("{}\n", clause.to_string(heap));
    }
    println!("\n=== Top Program ({} clauses) ===", top_program.len());
    println!("{buffer}");
    buffer
}
