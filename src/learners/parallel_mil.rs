use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc, Arc,
    },
    thread,
};

use crate::{
    app::{App, TopProg},
    heap::{
        Cell, Heap, QueryHeap,
        Tag::Ref,
        VarBind::{Addr, Var},
        VarReg,
    },
    learners::{
        predicate_unification::{PredDef, PredDefTable, MAX_PRED_DEFS},
        utils::parse_example,
    },
    program::{clause::Clause, meta_sub::MetaSub, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};

use super::{
    specialise::specialise_h,
    sub_h_unification::least_sub_h,
    utils::{collect_used_pred, reduce as reduce_hypothesis, union_sub_hypotheses},
};

use lazy_static::lazy_static;

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
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
        // Checked once, here, rather than left to fail deep in the search: a
        // hypothesis can invent at most one predicate per clause, and the
        // dependency graph that orders their definitions holds
        // `MAX_PRED_DEFS` nodes.
        assert!(
            self.config.max_clause <= MAX_PRED_DEFS,
            "max_clause is {}, but top program construction supports at most {MAX_PRED_DEFS}: \
             a sub hypothesis of that size could invent more predicates than the dependency \
             graph used to order their definitions can hold",
            self.config.max_clause,
        );
        println!("=== Top Program Construction ===");
        println!(
            "Positive examples: {}, Negative examples: {}",
            examples.pos.len(),
            examples.neg.len()
        );
        examples.normalise_for_top_prog();

        let (cells, mut sub_hypotheses, pdt) = generalise(
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
        // Capture before the loop below consumes `pdt.pred_defs`. These are
        // the constants that mark a body literal as calling an invented
        // predicate rather than a background one.
        let pred_symbols = pdt.pred_symbols().clone();

        for pred_def in pdt.pred_defs {
            for meta_sub in pred_def.meta_subs {
                let clause = meta_sub
                    .build_clause(&mut self.prog_heap, &self.predicate_table)
                    .expect("every MetaSub's meta clause id comes from the predicate table");
                let symbol_arity = self.prog_heap.symbol_arity(clause.head());
                self.predicate_table
                    .add_clause_to_predicate(clause, symbol_arity)
                    .unwrap();
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
        let Some(groups) = least_sub_h(
            &examples.pos,
            &examples.neg,
            sub_hypotheses,
            &self.prog_heap,
            &self.predicate_table,
            self.config,
            &pred_symbols,
        ) else {
            println!("No Valid Hypothesis Found");
            return None;
        };
        let mut buffer = Vec::new();
        for (i, group) in groups.into_iter().enumerate() {
            println!("Program {i}");
            // Sub hypotheses in a group routinely share clauses, so union
            // rather than concatenate.
            let mut top_program = union_sub_hypotheses(group, &self.prog_heap);

            // Reduce before collecting the invented predicates' definitions.
            // Afterwards those definitions are in the clause list *and* still
            // in the predicate table, so dropping one from the list would not
            // make anything unprovable and reduce would strip every one of
            // them as redundant.
            if reduce {
                top_program = reduce_hypothesis(
                    &examples.pos,
                    top_program,
                    &self.prog_heap,
                    &self.predicate_table,
                    self.config,
                    true,
                );
            }

            collect_used_pred(
                &mut top_program,
                &self.prog_heap,
                &self.predicate_table,
                &pred_symbols,
            );
            buffer.push(top_prog_to_string(top_program, &self.prog_heap));
        }
        Some(buffer)
    }
}

/// One worker thread's output from [`generalise_thread`]: the clause sets it
/// found, the predicate definitions extracted out of them, and the
/// `(cells, var_regs)` of the thread-local heap they both reference.
type ThreadResult = (Vec<Box<[Clause]>>, Vec<PredDef>, (Vec<Cell>, Vec<VarReg>));

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

    let (tx, rx) = mpsc::channel();
    let total = pos_examples.len();
    let completed = Arc::new(AtomicUsize::new(0));
    // The merge loop reports on the producers as well as itself, so it needs
    // its own handle on the counter: one writer to the status line, since
    // both sides would otherwise be overwriting the same `\r`-terminated row.
    let generalised = Arc::clone(&completed);

    // Producer threads run in the background on a scoped thread while the
    // calling thread merges each result as it arrives over `rx`.
    let result = thread::scope(|scope| {
        scope.spawn(move || {
            pool.scope(|s| {
                for example in pos_examples {
                    let tx = tx.clone();
                    let completed = Arc::clone(&completed);
                    s.spawn(move |_| {
                        let result = generalise_thread(example, predicate_table, heap, config);
                        // Counted before the send so the status line can never
                        // show more results merged than generalised.
                        completed.fetch_add(1, Ordering::Relaxed);
                        let _ = tx.send(result);
                    });
                }
            });
            // `tx` itself drops here, after every clone has already been
            // sent and dropped, closing the channel for `merge_thread_results`.
        });

        merge_thread_results(rx, heap, total, &generalised)
    });
    eprintln!();

    result
}

/// Fold every worker thread's [`ThreadResult`] into the final program-level
/// heap, predicate definition table, and deduplicated set of hypotheses.
///
/// `heap` is the real, already-populated program heap (`App::prog_heap`
/// before the caller appends `cells` onto it), so every address this
/// function returns -- clause literals, `PredDefTable` bindings, and the
/// returned `cells`' own addresses -- is already a valid absolute index
/// into the eventual combined `heap ++ cells`.
///
/// Each result is folded in as one "message" against a single accumulator
/// heap (`acc_heap`):
///   - its cells are appended, shifted by `acc_heap`'s current length;
///   - its `pred_defs` are fed through `PredDefTable::insert`, which grounds
///     its predicate variables (coining a fresh constant or unifying onto an
///     existing definition);
///   - any `Ref` cell still unbound after that is a predicate variable
///     nothing managed to ground, which is a bug -- panic;
///   - its `var_regs` are *not* relocated: each thread numbers its own
///     variables from 0, so `acc_heap.var_regs` is reused as a 0-based
///     scratch window (grown as needed, reset to `UNBOUND` after each
///     message) rather than given a fresh offset range.
///
/// Duplicate hypotheses -- clause sets that print identically once grounded
/// -- are dropped from the returned list; their now-orphaned cells are left
/// in place rather than reclaimed.
fn merge_thread_results(
    thread_results: impl IntoIterator<Item = ThreadResult>,
    heap: &[Cell],
    total: usize,
    generalised: &AtomicUsize,
) -> (Vec<Cell>, Vec<Box<[Clause]>>, PredDefTable) {
    let mut acc_heap = QueryHeap::new(heap, None);
    let mut pdt = PredDefTable::default();
    let mut hypotheses = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();

    for (merged, (clause_sets, pred_defs, (cells, var_regs))) in
        thread_results.into_iter().enumerate()
    {
        let offset = acc_heap.heap_len();
        if var_regs.len() > acc_heap.var_regs.len() {
            acc_heap.var_regs.resize(var_regs.len(), VarReg::UNBOUND);
        }

        acc_heap.cells.extend_from_slice(&cells);

        for mut pred_def in pred_defs {
            for meta_sub in &mut pred_def.meta_subs {
                meta_sub.shift_addrs(offset as isize);
            }
            pdt.insert(pred_def, &mut acc_heap);
        }

        for addr in offset..acc_heap.heap_len() {
            if acc_heap[addr].0 == Ref {
                let resolved = acc_heap.get_deref_cell(addr);
                if resolved.0 == Ref {
                    panic!("Not all variable predicates given constant terms");
                }
                acc_heap[addr] = resolved;
            }
        }

        for var_reg in &mut acc_heap.var_regs[..var_regs.len()] {
            *var_reg = VarReg::UNBOUND;
        }

        for clauses in clause_sets {
            let mut clauses = clauses.into_vec();
            for clause in &mut clauses {
                clause.shift_literals(offset);
            }
            let key = dedup_key(&clauses, &acc_heap);
            if seen.insert(key) {
                hypotheses.push(clauses.into_boxed_slice());
            }
        }

        // Merging runs on this thread while the producers are still going, so
        // report both: generalisation reaching `total` is not the end of the
        // work, and folding one result in can take longer than finding it.
        eprint!(
            "\rGeneralise: {}/{total} examples, merged: {}/{total}, {} predicate definitions  ",
            generalised.load(Ordering::Relaxed),
            merged + 1,
            pdt.pred_defs.len()
        );
        let _ = io::stderr().flush();
    }

    (acc_heap.cells, hypotheses, pdt)
}

/// Canonical string key for a hypothesis, used to drop duplicate clause sets
/// found across different positive examples (or different backtracked
/// solutions of the same example).
fn dedup_key(clauses: &[Clause], heap: &impl Heap) -> String {
    let mut literals: Vec<String> = clauses
        .iter()
        .map(|clause| clause.to_string(heap))
        .collect();
    literals.sort();
    literals.concat()
}

/// Search for hypotheses explaining one positive example, accumulating every
/// hypothesis found (across backtracking) into a single heap local to this
/// thread.
///
/// Duplicate hypotheses (backtracking solutions that print identically via
/// [`dedup_key`]) are dropped here so the channel and collector never see
/// them.
///
/// Returns the deduplicated clause sets (with predicate definitions extracted
/// out), the predicate definitions themselves ordered by dependency, and the
/// heap that both rely on. See [`extract_hypothesis`] for how a single
/// proof's hypothesis is folded into this thread-local heap.
fn generalise_thread(
    example: &str,
    predicate_table: &PredicateTable,
    prog_heap: &[Cell],
    config: Config,
) -> ThreadResult {
    let mut query_heap = QueryHeap::new(prog_heap, None);
    let mut dst = QueryHeap::new(&[], None);
    let mut clause_sets = Vec::new();
    let mut pred_defs = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();

    let goal = match parse_example(example, &mut query_heap) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Failed to parse example '{}': {}", example, e);
            return (clause_sets, pred_defs, (dst.cells, dst.var_regs));
        }
    };
    let mut proof = Proof::new(&query_heap, &[goal]);

    while proof.prove(&mut query_heap, predicate_table, config) {
        let (clauses, defs) = extract_hypothesis(&proof, &query_heap, &mut dst);
        if seen.insert(dedup_key(&clauses, &dst)) {
            clause_sets.push(clauses);
            pred_defs.extend(defs);
        }
    }

    (clause_sets, pred_defs, (dst.cells, dst.var_regs))
}

/// Extract one just-succeeded proof's hypothesis into `dst`, splitting it into
/// the predicate definitions it invents and the ordinary clauses left over.
///
/// `dst` is expected to persist across every hypothesis a worker thread finds
/// (see [`generalise_thread`]), so that one thread's clauses and predicate
/// definitions end up sharing a single heap. Each call still builds its own
/// fresh `ref_map`: two solutions of the same proof must not be treated as
/// sharing variable identity just because backtracking reused the same
/// proof-heap var ids for both.
fn extract_hypothesis(
    proof: &Proof,
    proof_heap: &QueryHeap,
    dst: &mut QueryHeap,
) -> (Box<[Clause]>, Vec<PredDef>) {
    let mut ref_map = HashMap::new();
    let mut clauses = Vec::with_capacity(proof.hypothesis.len());
    let mut meta_subs = Vec::with_capacity(proof.hypothesis.len());

    for (clause, meta_sub) in proof
        .hypothesis
        .iter()
        .zip(proof.hypothesis.meta_subs.iter())
    {
        let new_literals: Vec<usize> = clause
            .iter()
            .map(|&lit_addr| {
                let addr = dst.heap_len();
                dst.clone_term_from_other(proof_heap, lit_addr, &mut ref_map);
                addr
            })
            .collect();
        clauses.push(Clause::new(new_literals, None, clause.max_arg_id));
        meta_subs.push(clone_meta_sub(dst, proof_heap, meta_sub, &mut ref_map));
    }

    let pred_defs = PredDef::extract_pred_defs_from_h(&mut clauses, &mut meta_subs, &*dst);
    (clauses.into_boxed_slice(), pred_defs)
}

/// Translate one clause's compacted meta-variable substitution from
/// `proof_heap`'s address space into `dst`'s, sharing `ref_map` with the
/// clause-literal cloning so a predicate variable named in both a clause head
/// and its `MetaSub` lands on the same destination variable.
fn clone_meta_sub(
    dst: &mut QueryHeap,
    proof_heap: &QueryHeap,
    meta_sub: &MetaSub,
    ref_map: &mut HashMap<usize, usize>,
) -> MetaSub {
    let subs = meta_sub
        .subs
        .iter()
        .map(|&var_reg| clone_var_reg(dst, proof_heap, var_reg, ref_map))
        .collect();
    MetaSub {
        meta_clause_id: meta_sub.meta_clause_id,
        subs,
    }
}

/// Translate a single meta-sub binding from `proof_heap`'s address space into
/// `dst`'s.
///
/// A binding naming a heap address has its term cloned directly. One naming a
/// variable is dereferenced against `proof_heap` first -- a variable bound
/// since the `MetaSub` was recorded now resolves to an address, which must be
/// cloned rather than left as a stale variable reference -- and only mapped
/// through `ref_map` if it is still unbound.
fn clone_var_reg(
    dst: &mut QueryHeap,
    proof_heap: &QueryHeap,
    var_reg: VarReg,
    ref_map: &mut HashMap<usize, usize>,
) -> VarReg {
    let binding = var_reg
        .get_bind()
        .expect("MetaSub subs are always populated from bound arg registers");
    let resolved = match binding {
        Var(var_id) => proof_heap.var_deref(var_id),
        bound @ Addr(_) => bound,
    };
    match resolved {
        Addr(addr) => {
            let new_addr = dst.heap_len();
            dst.clone_term_from_other(proof_heap, addr, ref_map);
            VarReg::from_addr(new_addr)
        }
        Var(var_id) => {
            let new_var_id = *ref_map
                .entry(var_id)
                .or_insert_with(|| dst.new_var(VarReg::UNBOUND));
            VarReg::from_var(new_var_id)
        }
    }
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
                let keep = specialise_h(neg_examples, hypothesis, heap, predicate_table, config);
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

fn top_prog_to_string(top_program: Vec<Clause>, heap: &impl Heap) -> String {
    let mut buffer = String::new();
    for clause in &top_program {
        buffer += &format!("{}\n", clause.to_string(heap));
    }
    println!("\n=== Top Program ({} clauses) ===", top_program.len());
    println!("{buffer}");
    buffer
}

#[cfg(test)]
mod extraction_tests {
    use super::*;
    use crate::heap::{
        SymbolDB,
        Tag::{Comp, Con},
    };

    /// Build a `Proof` with no goals (so it never actually resolves anything)
    /// whose `hypothesis` field is pre-populated with `clauses`/`meta_subs`.
    /// Good enough to exercise [`extract_hypothesis`], which only ever reads
    /// `proof.hypothesis`.
    fn proof_with_hypothesis<'a>(
        proof_heap: &QueryHeap,
        clauses: Vec<Clause>,
        meta_subs: Vec<MetaSub>,
    ) -> Proof<'a> {
        let mut proof = Proof::new(proof_heap, &[]);
        proof.hypothesis.clauses = clauses;
        proof.hypothesis.meta_subs = meta_subs;
        proof
    }

    #[test]
    fn clone_var_reg_reuses_ref_map_for_repeated_unbound_variable() {
        let mut proof_heap = QueryHeap::new(&[], None);
        let v = proof_heap.new_var(VarReg::UNBOUND);
        let mut dst = QueryHeap::new(&[], None);
        let mut ref_map = HashMap::new();

        let first = clone_var_reg(&mut dst, &proof_heap, VarReg::from_var(v), &mut ref_map);
        let second = clone_var_reg(&mut dst, &proof_heap, VarReg::from_var(v), &mut ref_map);

        assert!(
            first.var(),
            "an unbound variable should clone to another variable"
        );
        assert_eq!(
            first, second,
            "repeated occurrences of the same source variable must map to the same destination variable"
        );
    }

    #[test]
    fn clone_var_reg_clones_a_direct_address_binding() {
        let mut proof_heap = QueryHeap::new(&[], None);
        let sym = SymbolDB::set_const("q");
        let addr_q = proof_heap.heap_push((Con, sym));

        let mut dst = QueryHeap::new(&[], None);
        let mut ref_map = HashMap::new();

        let cloned = clone_var_reg(
            &mut dst,
            &proof_heap,
            VarReg::from_addr(addr_q),
            &mut ref_map,
        );

        assert!(cloned.addr());
        assert_eq!(dst[cloned.value()], (Con, sym));
    }

    #[test]
    fn clone_var_reg_inlines_a_variable_bound_since_the_meta_sub_was_recorded() {
        // Simulates a MetaSub recorded while an arg register was still an
        // unbound variable, with the proof later binding that variable to an
        // address before extraction runs.
        let mut proof_heap = QueryHeap::new(&[], None);
        let sym = SymbolDB::set_const("p");
        let addr_p = proof_heap.heap_push((Con, sym));
        let v = proof_heap.new_var(VarReg::UNBOUND);
        proof_heap.bind(v, Addr(addr_p));

        let mut dst = QueryHeap::new(&[], None);
        let mut ref_map = HashMap::new();

        let cloned = clone_var_reg(&mut dst, &proof_heap, VarReg::from_var(v), &mut ref_map);

        assert!(
            cloned.addr(),
            "a variable bound to an address must be inlined, not left as a stale variable reference"
        );
        assert_eq!(dst[cloned.value()], (Con, sym));
    }

    #[test]
    fn clone_meta_sub_preserves_meta_clause_id_and_translates_subs() {
        let mut proof_heap = QueryHeap::new(&[], None);
        let v1 = proof_heap.new_var(VarReg::UNBOUND);
        let v2 = proof_heap.new_var(VarReg::UNBOUND);
        let meta_sub = MetaSub {
            meta_clause_id: 7,
            subs: vec![VarReg::from_var(v1), VarReg::from_var(v2)],
        };

        let mut dst = QueryHeap::new(&[], None);
        let mut ref_map = HashMap::new();
        let cloned = clone_meta_sub(&mut dst, &proof_heap, &meta_sub, &mut ref_map);

        assert_eq!(cloned.meta_clause_id, 7);
        assert_eq!(cloned.subs.len(), 2);
        assert!(cloned.subs[0].var() && cloned.subs[1].var());
        assert_ne!(
            cloned.subs[0], cloned.subs[1],
            "distinct source variables should map to distinct destination variables"
        );
    }

    #[test]
    fn extract_hypothesis_leaves_ordinary_clauses_untouched_by_pred_def_extraction() {
        // A fact headed by a *constant* predicate `p` (`(Comp, 1), (Con, p)`,
        // i.e. a 0-ary predicate: a Comp's arity counts the functor cell
        // itself). `PredDef::extract_pred_defs_from_h` only lifts clauses
        // whose functor cell is a predicate *variable*, so this must be left
        // as an ordinary clause.
        let mut proof_heap = QueryHeap::new(&[], None);
        let sym = SymbolDB::set_const("p");
        let head_addr = proof_heap.heap_len();
        proof_heap.heap_push((Comp, 1));
        proof_heap.heap_push((Con, sym));
        let clause = Clause::new(vec![head_addr], None, 0);
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: vec![],
        };

        let proof = proof_with_hypothesis(&proof_heap, vec![clause], vec![meta_sub]);
        let mut dst = QueryHeap::new(&[], None);
        let (clauses, pred_defs) = extract_hypothesis(&proof, &proof_heap, &mut dst);

        assert!(pred_defs.is_empty());
        assert_eq!(clauses.len(), 1);
        assert_eq!(dst[clauses[0].head()], (Comp, 1));
        assert_eq!(dst[clauses[0].head() + 1], (Con, sym));
    }

    #[test]
    fn extract_hypothesis_shares_variable_identity_between_clause_and_meta_sub() {
        // `pred_var(arg_var).` with `arg_var` also recorded in the clause's
        // MetaSub -- the clause head is a predicate-variable-headed Comp, so
        // this should be lifted into a PredDef rather than kept as an
        // ordinary clause.
        let mut proof_heap = QueryHeap::new(&[], None);
        let pred_var = proof_heap.new_var(VarReg::UNBOUND);
        let arg_var = proof_heap.new_var(VarReg::UNBOUND);
        let head_addr = proof_heap.heap_len();
        proof_heap.heap_push((Comp, 2));
        proof_heap.heap_push((Ref, pred_var));
        proof_heap.heap_push((Ref, arg_var));

        let clause = Clause::new(vec![head_addr], None, 0);
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: vec![VarReg::from_var(arg_var)],
        };

        let proof = proof_with_hypothesis(&proof_heap, vec![clause], vec![meta_sub]);
        let mut dst = QueryHeap::new(&[], None);
        let (clauses, pred_defs) = extract_hypothesis(&proof, &proof_heap, &mut dst);

        assert!(
            clauses.is_empty(),
            "a predicate-variable-headed clause should be lifted into a PredDef"
        );
        assert_eq!(pred_defs.len(), 1);
        assert_eq!(pred_defs[0].meta_subs.len(), 1);

        // The clause's literal was cloned first, so it occupies dst[0..=2].
        let (comp_tag, comp_arity) = dst[0];
        assert_eq!((comp_tag, comp_arity), (Comp, 2));
        let (arg_tag, cloned_arg_var) = dst[2];
        assert_eq!(arg_tag, Ref);

        assert_eq!(
            pred_defs[0].meta_subs[0].subs[0],
            VarReg::from_var(cloned_arg_var),
            "the meta sub's argument binding should name the same destination \
             variable as the clause's own argument occurrence"
        );
    }

    #[test]
    fn extract_hypothesis_uses_a_fresh_ref_map_each_call() {
        // Two "solutions" of the same proof can legitimately reuse the same
        // proof-heap var id (backtracking resets and reassigns registers).
        // Each call to `extract_hypothesis` must still land on a distinct
        // destination variable rather than aliasing the two solutions. Use a
        // predicate-variable-headed clause so the shared identity shows up on
        // the extracted `PredDef`'s meta sub.
        let mut proof_heap = QueryHeap::new(&[], None);
        let pred_var = proof_heap.new_var(VarReg::UNBOUND);
        let head_addr = proof_heap.heap_len();
        proof_heap.heap_push((Comp, 1));
        proof_heap.heap_push((Ref, pred_var));
        let clause = Clause::new(vec![head_addr], None, 0);
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: vec![VarReg::from_var(pred_var)],
        };

        let mut dst = QueryHeap::new(&[], None);

        let proof1 =
            proof_with_hypothesis(&proof_heap, vec![clause.clone()], vec![meta_sub.clone()]);
        let (_, pred_defs1) = extract_hypothesis(&proof1, &proof_heap, &mut dst);

        let proof2 = proof_with_hypothesis(&proof_heap, vec![clause], vec![meta_sub]);
        let (_, pred_defs2) = extract_hypothesis(&proof2, &proof_heap, &mut dst);

        let var1 = pred_defs1[0].meta_subs[0].subs[0];
        let var2 = pred_defs2[0].meta_subs[0].subs[0];

        assert_ne!(
            var1, var2,
            "each proof solution should get a distinct destination variable, \
             even though both reference the same proof-heap var id"
        );
    }
}

#[cfg(test)]
mod merge_tests {
    use super::*;
    use crate::heap::{
        SymbolDB,
        Tag::{Comp, Con},
    };

    /// [`merge_thread_results`] with the progress-reporting arguments filled
    /// in: these tests supply every message up front, so "generalised" is
    /// simply the message count.
    fn merge(
        results: Vec<ThreadResult>,
        heap: &[Cell],
    ) -> (Vec<Cell>, Vec<Box<[Clause]>>, PredDefTable) {
        let total = results.len();
        merge_thread_results(results, heap, total, &AtomicUsize::new(total))
    }
    use smallvec::smallvec;

    /// A fresh, 0-indexed thread-local heap to build a test's clauses and
    /// predicate definitions against.
    fn thread_heap() -> QueryHeap<'static> {
        QueryHeap::new(&[], None)
    }

    /// Deconstruct a thread-local heap into the `(cells, var_regs)` pair
    /// `generalise_thread` actually returns.
    fn parts(heap: QueryHeap<'static>) -> (Vec<Cell>, Vec<VarReg>) {
        (heap.cells, heap.var_regs)
    }

    #[test]
    fn merge_grounds_a_pred_defs_variable_and_the_orphaned_ref_cell_it_left_behind() {
        let mut heap = thread_heap();
        // Simulate the now-discarded head clause of an invented predicate:
        // `PredDef::extract_pred_defs_from_h` removes the `Clause` from the
        // hypothesis but the literal's cells it already cloned into the
        // thread's heap are left behind, orphaned.
        let pred_var = heap.new_var(VarReg::UNBOUND);
        heap.heap_push((Comp, 1));
        heap.heap_push((Ref, pred_var));

        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: vec![VarReg::from_var(pred_var)],
        };
        let pred_def = PredDef::new(smallvec![meta_sub]);

        let (cells, hypotheses, pdt) = merge(vec![(Vec::new(), vec![pred_def], parts(heap))], &[]);

        assert!(hypotheses.is_empty());
        for (i, cell) in cells.iter().enumerate() {
            assert_ne!(cell.0, Ref, "cell {i} ({cell:?}) should have been grounded");
        }
        assert_eq!(cells[0], (Comp, 1));
        // The orphaned `(Ref, pred_var)` cell (index 1) must have been
        // grounded to the same constant the pred_def's own binding (which
        // `make_const` pushed as a fresh cell at index 2) resolves to.
        assert_eq!(cells[1], cells[2]);
        assert_eq!(cells[2].0, Con);

        assert_eq!(pdt.pred_defs.len(), 1);
        assert_eq!(pdt.pred_defs[0].meta_subs[0].subs[0], VarReg::from_addr(2));
    }

    #[test]
    fn merge_grounds_each_messages_predicate_variable_independently() {
        // Two messages, each inventing an unrelated nullary predicate and
        // each numbering its own predicate variable from 0 -- exercising
        // that the scratch window gets reset between messages rather than
        // leaking a stale binding from the first message into the second.
        let make_message = |meta_clause_id: usize| {
            let mut heap = thread_heap();
            let pred_var = heap.new_var(VarReg::UNBOUND);
            heap.heap_push((Comp, 1));
            heap.heap_push((Ref, pred_var));
            let meta_sub = MetaSub {
                meta_clause_id,
                subs: vec![VarReg::from_var(pred_var)],
            };
            let pred_def = PredDef::new(smallvec![meta_sub]);
            (Vec::new(), vec![pred_def], parts(heap))
        };

        let (cells, hypotheses, pdt) = merge(vec![make_message(0), make_message(1)], &[]);

        assert!(hypotheses.is_empty());
        assert_eq!(
            pdt.pred_defs.len(),
            2,
            "distinct meta_clause_ids should not unify together"
        );
        for (i, cell) in cells.iter().enumerate() {
            assert_ne!(cell.0, Ref, "cell {i} ({cell:?}) should have been grounded");
        }

        // Each message coined its own fresh constant; they must not alias.
        let (first_const_addr, _) = pdt.pred_defs[0].meta_subs[0].subs[0]
            .get_bind()
            .and_then(|b| if let Addr(a) = b { Some((a, ())) } else { None })
            .expect("first pred_def's binding should be a resolved address");
        let (second_const_addr, _) = pdt.pred_defs[1].meta_subs[0].subs[0]
            .get_bind()
            .and_then(|b| if let Addr(a) = b { Some((a, ())) } else { None })
            .expect("second pred_def's binding should be a resolved address");
        assert_ne!(cells[first_const_addr], cells[second_const_addr]);
    }

    #[test]
    fn merge_shifts_clause_literal_addresses_between_messages() {
        let sym_p = SymbolDB::set_const("merge_test_shift_p");
        let sym_q = SymbolDB::set_const("merge_test_shift_q");

        let message = |sym: usize| {
            let mut heap = thread_heap();
            let head = heap.heap_push((Comp, 1));
            heap.heap_push((Con, sym));
            let clauses: Vec<Box<[Clause]>> = vec![Box::from([Clause::new(vec![head], None, 0)])];
            (clauses, Vec::new(), parts(heap))
        };

        let (cells, hypotheses, _) = merge(vec![message(sym_p), message(sym_q)], &[]);

        assert_eq!(
            cells,
            vec![(Comp, 1), (Con, sym_p), (Comp, 1), (Con, sym_q)]
        );
        assert_eq!(hypotheses.len(), 2);
        assert_eq!(hypotheses[0][0].head(), 0, "first message is not shifted");
        assert_eq!(
            hypotheses[1][0].head(),
            2,
            "second message's clause literal should be shifted past the first message's cells"
        );
    }

    #[test]
    fn merge_drops_duplicate_hypotheses_found_across_messages() {
        let sym_p = SymbolDB::set_const("merge_test_dup_p");

        let message = || {
            let mut heap = thread_heap();
            let head = heap.heap_push((Comp, 1));
            heap.heap_push((Con, sym_p));
            let clauses: Vec<Box<[Clause]>> = vec![Box::from([Clause::new(vec![head], None, 0)])];
            (clauses, Vec::new(), parts(heap))
        };

        let (cells, hypotheses, _) = merge(vec![message(), message()], &[]);

        assert_eq!(
            hypotheses.len(),
            1,
            "the second message's identical hypothesis should be deduplicated"
        );
        // The duplicate's cells are still appended (not reclaimed), only the
        // returned hypothesis list is deduplicated.
        assert_eq!(cells.len(), 4);
    }

    #[test]
    #[should_panic(expected = "Not all variable predicates given constant terms")]
    fn merge_panics_if_a_ref_cell_survives_grounding() {
        // A `Ref` cell with no pred_def (and so nothing to ground it) must
        // trip the same guard `App::run_top_prog` relies on never firing.
        let mut heap = thread_heap();
        let stray_var = heap.new_var(VarReg::UNBOUND);
        heap.heap_push((Ref, stray_var));

        let _ = merge(vec![(Vec::new(), Vec::new(), parts(heap))], &[]);
    }
}
