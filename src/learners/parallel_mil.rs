use std::{
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc, Arc,
    },
    thread,
};

use crate::{
    app::App,
    heap::{
        Cell, Heap, ProgramHeap, QueryHeap,
        Tag::{Con, ELis, Flt, Int, Stri, Var},
        TermWalk,
        VarBind::{Addr, VarId},
        VarReg, Walk,
    },
    learners::predicate_unification::{PredDef, PredDefTable, MAX_PRED_DEFS},
    program::{Clause, MetaSub, MetaSubGroup, MetaSubTrait, PackedMetaSubs, PredicateTable},
    resolution::Proof,
    Config,
};

use super::{
    specialise::specialise,
    sub_h_unification::{least_sub_h, SearchCtx},
    utils::{
        collect_used_pred, compile_examples, reduce as reduce_hypothesis, union_sub_hypotheses,
    },
};

use lazy_static::lazy_static;
use smallvec::SmallVec;

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

type SmallH = SmallVec<[MetaSub; 1]>;

impl App {
    pub fn run_parallel(&mut self) -> Option<Vec<String>> {
        let Some(mut examples) = self.examples.clone() else {
            panic!("Can't start top prog without examples");
        };
        // Called directly as well as through `App::run`, which only reaches
        // here when `parallel` is set -- so a direct caller that has not set
        // it gets the defaults rather than a panic.
        let parallel = self.parallel.unwrap_or_default();
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
        examples.normalise_for_parallel();

        // Built once onto the program heap, then proved over and over by
        // every stage below. Appending leaves earlier addresses valid, so the
        // learned clauses added later do not disturb these.
        let pos_goals = compile_examples(&examples.pos, &mut self.prog_heap);
        let neg_goals = compile_examples(&examples.neg, &mut self.prog_heap);

        let (cells, hypotheses, pdt) = generalise(
            &pos_goals,
            &self.predicate_table,
            &self.prog_heap,
            self.config,
        );

        for (i, cell) in cells.iter().enumerate() {
            if cell.0 == Var {
                panic!("{cell:?}@{i}\n{:?}", &cells[i - 5..i + 5])
            }
        }

        // TODO consider more effecient method for adding pdt clauses to program
        self.prog_heap.extend_from_slice(&cells);
        // Capture before the loop below consumes `pdt.pred_defs`. These are
        // the constants that mark a body literal as calling an invented
        // predicate rather than a background one.
        let pred_symbols = pdt.pred_symbols().clone();

        // Added as one batch: one insert per clause rescans the whole table.
        // Most definitions have one or two clauses.
        let mut pred_def_clauses = Vec::with_capacity(pdt.len() * 2);
        for pred_def in pdt.iter() {
            for meta_sub in pred_def.iter() {
                let clause = meta_sub
                    .build_clause(&mut self.prog_heap, &self.predicate_table)
                    .expect("every MetaSub's meta clause id comes from the predicate table");
                let symbol_arity = self.prog_heap.symbol_arity(clause.head());
                pred_def_clauses.push((symbol_arity, clause));
            }
        }
        self.predicate_table.add_clauses(pred_def_clauses).unwrap();
        drop(pdt);

        // Literals are built only here; until now hypotheses were `MetaSub`s.
        let sub_hypotheses: Vec<Box<[Clause]>> = hypotheses
            .iter()
            .map(|meta_subs| {
                meta_subs
                    .iter()
                    .map(|meta_sub| {
                        meta_sub
                            .build_clause(&mut self.prog_heap, &self.predicate_table)
                            .expect("every MetaSub's meta clause id comes from the predicate table")
                    })
                    .collect()
            })
            .collect();
        drop(hypotheses);

        println!(
            "\n=== Generalisation ===\n{} unique sub hypotheses",
            sub_hypotheses.len(),
        );

        // The invented predicates' definitions are in the predicate table
        // now, which is what lets specialisation (and every later stage)
        // prove goals on them like any other call.
        let found = sub_hypotheses.len();
        let sub_hypotheses = specialise(
            &neg_goals,
            sub_hypotheses,
            &self.prog_heap,
            &self.predicate_table,
            self.config,
        );
        println!(
            "=== Specialisation ===\n{} of {found} hypotheses consistent with all {} negatives",
            sub_hypotheses.len(),
            neg_goals.len(),
        );

        // Build final top program from surviving hypotheses
        let Some(groups) = least_sub_h(
            &pos_goals,
            &neg_goals,
            sub_hypotheses,
            SearchCtx::new(
                &self.prog_heap,
                &self.predicate_table,
                self.config,
                parallel,
            ),
            &pred_symbols,
        ) else {
            println!("No Valid Hypothesis Found");
            return None;
        };

        let hypotheses: Vec<Vec<Clause>> = groups
            .into_iter()
            .map(|group| {
                let mut hypothesis = union_sub_hypotheses(group, &self.prog_heap);
                collect_used_pred(
                    &mut hypothesis,
                    &self.prog_heap,
                    &self.predicate_table,
                    &pred_symbols,
                );
                hypothesis
            })
            .collect();

        let mut buffer = Vec::new();
        for (i, mut hypothesis) in hypotheses.into_iter().enumerate() {
            println!("Hypothesis {i}");

            //Remove used preds from predicate table for reduction
            for clause in &hypothesis {
                for literal in clause.iter() {
                    let (symbol, arity) = self.prog_heap.symbol_arity(*literal);
                    if pred_symbols.contains(&symbol) {
                        self.predicate_table.remove_predicate((symbol, arity));
                    }
                }
            }

            if parallel.reduce {
                hypothesis = reduce_hypothesis(
                    &pos_goals,
                    hypothesis,
                    &self.prog_heap,
                    &self.predicate_table,
                    self.config,
                    true,
                );
            }

            buffer.push(top_prog_to_string(hypothesis, &self.prog_heap));
        }
        Some(buffer)
    }
}

/// One sub hypothesis as sent from a worker: the hypothesis as `MetaSub`s,
/// the predicate definitions it depends on, and the `(cells, var_regs)` of
/// the detached heap their terms live on.
type ThreadResult = (SmallH, Vec<PredDef>, (Vec<Cell>, Vec<VarReg>));

/// Most sub hypotheses that can wait for the collector at once.
///
/// A worker that finds the channel full blocks until the collector catches
/// up, so a search that outruns the merge slows down instead of queueing
/// messages without limit.
const CHANNEL_CAPACITY: usize = 4096;

/// Search every positive example in parallel, streaming each sub hypothesis
/// found back to this thread as it is extracted.
///
/// One worker per positive example (see [`generalise_thread`]). Each
/// hypothesis is folded into the shared predicate definition table by
/// [`merge_thread_results`] the moment it arrives, so grounding and
/// deduplication overlap with the search instead of waiting on it.
fn generalise(
    pos_goals: &[usize],
    predicate_table: &PredicateTable,
    heap: &ProgramHeap,
    config: Config,
) -> (Vec<Cell>, PackedMetaSubs, PredDefTable) {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT - 1)
        .build()
        .unwrap();

    let (tx, rx) = mpsc::sync_channel(CHANNEL_CAPACITY);
    let total = pos_goals.len();
    let completed = Arc::new(AtomicUsize::new(0));
    // The merge loop reports on the producers as well as itself, so it needs
    // its own handle on the counter: one writer to the status line, since
    // both sides would otherwise be overwriting the same `\r`-terminated row.
    let searched = Arc::clone(&completed);

    // Producer threads run in the background on a scoped thread while the
    // calling thread merges each hypothesis as it arrives over `rx`.
    let result = thread::scope(|scope| {
        scope.spawn(move || {
            pool.scope(|s| {
                for &goal in pos_goals {
                    let tx = tx.clone();
                    let completed = Arc::clone(&completed);
                    s.spawn(move |_| {
                        generalise_thread(goal, predicate_table, heap, config, &tx);
                        completed.fetch_add(1, Ordering::Relaxed);
                    });
                }
            });
            // `tx` itself drops here, after every clone has already been
            // sent and dropped, closing the channel for `merge_thread_results`.
        });

        merge_thread_results(rx, heap, total, &searched)
    });
    eprintln!();

    result
}

/// Fold every streamed [`ThreadResult`] into the collector heap, predicate
/// definition table, and deduplicated list of hypotheses.
///
/// `heap` is the program heap the returned `cells` will be appended to, so
/// every returned address is already valid in `heap ++ cells`.
///
/// For each message:
///   - the terms its substitutions name are interned into the collector heap
///     (see [`TermIndex`]), so the message's own cells are never appended;
///   - its `pred_defs` go through `PredDefTable::insert`, grounding their
///     predicate variables;
///   - a `Ref` cell still unbound after that is a bug -- panic;
///   - the hypothesis's references to those predicates are rewritten from
///     variables to the grounded addresses, since `acc_heap.var_regs` is a
///     scratch window reset after every message;
///   - the hypothesis is dropped if an equal one was already collected.
///
/// Hypotheses are compared order-independently, by hash confirmed with an
/// exact check.
fn merge_thread_results(
    thread_results: impl IntoIterator<Item = ThreadResult>,
    heap: &ProgramHeap,
    total: usize,
    searched: &AtomicUsize,
) -> (Vec<Cell>, PackedMetaSubs, PredDefTable) {
    let mut acc_heap = QueryHeap::new(heap, None);
    let mut terms = TermIndex::default();
    // Rebuilt from each message's `(cells, var_regs)` so its terms can be read.
    let mut msg_heap = QueryHeap::detached(heap);
    let mut pdt = PredDefTable::default();
    let mut hypotheses = PackedMetaSubs::default();
    // Hypothesis content hash -> indices into `hypotheses`.
    let mut seen: HashMap<u64, SmallVec<[u32; 1]>> = HashMap::new();

    for (merged, (mut hypothesis, pred_defs, (cells, var_regs))) in
        thread_results.into_iter().enumerate()
    {
        let offset = acc_heap.heap_len();
        if var_regs.len() > acc_heap.var_regs.len() {
            acc_heap.var_regs.resize(var_regs.len(), VarReg::UNBOUND);
        }

        let var_count = var_regs.len();
        msg_heap.cells = cells;
        msg_heap.var_regs = var_regs;
        terms.start_message();

        // Before the scan below, which grounds any variables these terms hold.
        for meta_sub in &mut hypothesis {
            terms.intern_subs(meta_sub, &msg_heap, &mut acc_heap);
        }
        for mut pred_def in pred_defs {
            for meta_sub in &mut pred_def.meta_subs {
                terms.intern_subs(meta_sub, &msg_heap, &mut acc_heap);
            }
            pdt.insert(pred_def, &mut acc_heap);
        }

        for addr in offset..acc_heap.heap_len() {
            if acc_heap[addr].0 == Var {
                let resolved = acc_heap.get_deref_cell(addr);
                if resolved.0 == Var {
                    panic!("Not all variable predicates given constant terms");
                }
                acc_heap[addr] = resolved;
            }
        }

        // A sub still bound to a variable names a predicate grounded above.
        for meta_sub in &mut hypothesis {
            for sub in &mut meta_sub.subs {
                if let Some(VarId(var_id)) = sub.get_bind() {
                    match acc_heap.var_deref(var_id) {
                        bound @ Addr(_) => *sub = bound.into(),
                        VarId(_) => panic!("Not all variable predicates given constant terms"),
                    }
                }
            }
        }

        for var_reg in &mut acc_heap.var_regs[..var_count] {
            *var_reg = VarReg::UNBOUND;
        }

        // Empty when every clause was lifted into a predicate definition.
        if !hypothesis.is_empty() {
            // Sort so that clause order does not affect equality. Interned
            // terms have one address each, so addresses stand in for content.
            hypothesis.sort_unstable_by(|a, b| {
                a.meta_clause_id.cmp(&b.meta_clause_id).then_with(|| {
                    a.subs
                        .iter()
                        .map(|sub| sub.0)
                        .cmp(b.subs.iter().map(|sub| sub.0))
                })
            });
            let mut hasher = DefaultHasher::new();
            for meta_sub in &hypothesis {
                meta_sub.meta_clause_id.hash(&mut hasher);
                for sub in &meta_sub.subs {
                    sub.0.hash(&mut hasher);
                }
                // Separator between clauses.
                usize::MAX.hash(&mut hasher);
            }

            let bucket = seen.entry(hasher.finish()).or_default();
            let duplicate = bucket
                .iter()
                .any(|&i| same_hypothesis(hypotheses.get(i as usize), &hypothesis));
            if !duplicate {
                bucket
                    .push(u32::try_from(hypotheses.len()).expect("more than u32::MAX hypotheses"));
                hypotheses.push(&hypothesis);
            }
        }

        // One message per hypothesis is too many for the status line, so
        // repaint it only every so often; the caller prints the final state.
        if merged % 128 == 0 {
            eprint!(
                "\rGeneralise: {}/{total} examples searched, {} hypotheses merged \
                 ({} unique), {} predicate definitions  ",
                searched.load(Ordering::Relaxed),
                merged + 1,
                hypotheses.len(),
                pdt.len()
            );
            let _ = io::stderr().flush();
        }
    }

    (acc_heap.cells, hypotheses, pdt)
}

/// Index of the ground terms on the collector heap, so each distinct term a
/// worker sends is stored there once.
///
/// Keyed by content hash and confirmed with `term_equal`. Constants coined
/// for invented predicates are not indexed: workers only ever name those
/// through variables, so no incoming term can equal one.
#[derive(Default)]
struct TermIndex {
    /// `term_hash` -> collector addresses of the terms with that hash.
    buckets: HashMap<u64, SmallVec<[usize; 1]>>,
    /// Message address -> collector address, for the current message.
    memo: SmallVec<[(usize, usize); 8]>,
    /// Message variable ids mapped to themselves; see [`Self::intern`].
    var_map: HashMap<usize, usize>,
}

impl TermIndex {
    fn start_message(&mut self) {
        self.memo.clear();
        self.var_map.clear();
    }

    /// Rewrite each address in `meta_sub` from `msg_heap` to the collector
    /// address of an equal term. Variables are left alone.
    fn intern_subs(
        &mut self,
        meta_sub: &mut MetaSub,
        msg_heap: &QueryHeap,
        acc_heap: &mut QueryHeap,
    ) {
        for sub in &mut meta_sub.subs {
            if let Some(Addr(addr)) = sub.get_bind() {
                *sub = VarReg::from_addr(self.intern(addr, msg_heap, acc_heap));
            }
        }
    }

    /// Collector address of a term equal to the one at `addr` on `msg_heap`,
    /// copying it across only if there is none yet.
    fn intern(&mut self, addr: usize, msg_heap: &QueryHeap, acc_heap: &mut QueryHeap) -> usize {
        if let Some(&(_, interned)) = self.memo.iter().find(|(from, _)| *from == addr) {
            return interned;
        }

        let start = acc_heap.heap_len();
        let interned = if term_has_var(addr, msg_heap) {
            // Not ground until its predicate variables are, so it cannot be
            // shared: copy it, keeping the message's variable ids, which the
            // collector's scratch window uses as they are.
            if self.var_map.is_empty() {
                self.var_map
                    .extend((0..msg_heap.var_regs.len()).map(|id| (id, id)));
            }
            acc_heap.clone_term_from_other(msg_heap, addr, &mut self.var_map);
            start
        } else {
            let mut hasher = DefaultHasher::new();
            msg_heap.term_hash(addr, &mut hasher);
            let bucket = self.buckets.entry(hasher.finish()).or_default();

            // Copied first so the comparison is within one heap; a ground
            // term has no variables for the map to translate.
            acc_heap.clone_term_from_other(msg_heap, addr, &mut self.var_map);
            match bucket
                .iter()
                .find(|&&existing| acc_heap.term_equal(existing, start))
            {
                Some(&existing) => {
                    let copied = acc_heap.heap_len() - start;
                    acc_heap.cells.truncate(acc_heap.cells.len() - copied);
                    existing
                }
                None => {
                    bucket.push(start);
                    self.index_sub_terms(start, acc_heap);
                    start
                }
            }
        };

        self.memo.push((addr, interned));
        interned
    }

    /// Index the single-cell terms inside the term just copied to `start`, so
    /// a later message naming one of them alone can reuse its cell.
    fn index_sub_terms(&mut self, start: usize, acc_heap: &QueryHeap) {
        for addr in start + 1..acc_heap.heap_len() {
            if !matches!(acc_heap[addr].0, Con | Int | Flt | Stri | ELis) {
                continue;
            }
            let mut hasher = DefaultHasher::new();
            acc_heap.term_hash(addr, &mut hasher);
            let bucket = self.buckets.entry(hasher.finish()).or_default();
            if !bucket
                .iter()
                .any(|&existing| acc_heap.term_equal(existing, addr))
            {
                bucket.push(addr);
            }
        }
    }
}

/// Whether the term at `addr` contains an unbound variable.
fn term_has_var(addr: usize, heap: &QueryHeap) -> bool {
    let mut walk = TermWalk::new(addr);
    while let Some((tag, _)) = walk.next_cell(heap) {
        if tag == Var {
            return true;
        }
    }
    false
}

/// Whether two sorted, grounded hypotheses hold the same clauses, comparing
/// interned terms by address.
fn same_hypothesis(stored: MetaSubGroup, new: &[MetaSub]) -> bool {
    stored.len() == new.len()
        && stored.iter().zip(new).all(|(x, y)| {
            x.meta_clause_id() == y.meta_clause_id && x.subs().eq(y.subs.iter().copied())
        })
}

/// Search for hypotheses explaining one positive example, streaming each one
/// found (across backtracking) through `tx` as it is extracted.
///
/// Each hypothesis is extracted onto its own detached heap, so a message is
/// self-contained.
///
/// No deduplication happens here: invented predicates are still unbound
/// variables, so hypotheses differing only in how one is *defined* look
/// identical until the collector grounds them.
///
/// A send fails only if the collector has hung up, which it never does
/// while producers hold senders, so the result is ignored.
fn generalise_thread(
    goal: usize,
    predicate_table: &PredicateTable,
    prog_heap: &ProgramHeap,
    config: Config,
    tx: &mpsc::SyncSender<ThreadResult>,
) {
    let mut query_heap = QueryHeap::new(prog_heap, None);

    let mut proof = Proof::new(&query_heap, &[goal]);

    while proof.prove(&mut query_heap, predicate_table, config) {
        let mut dst = QueryHeap::detached(prog_heap);
        let (hypothesis, defs) = extract_hypothesis(&proof, &query_heap, &mut dst, predicate_table);
        let _ = tx.send((hypothesis, defs, (dst.cells, dst.var_regs)));
    }
}

/// Extract a succeeded proof's hypothesis into `dst` as `MetaSub`s, split
/// into the predicate definitions it invents and the hypothesis that depends
/// on them.
///
/// Only the substitutions are cloned; the clauses themselves are never read.
///
/// `ref_map` is fresh per call, since backtracking reuses proof-heap var ids
/// across solutions, but shared across the hypothesis's clauses so a
/// predicate variable named by several lands on one `dst` variable.
fn extract_hypothesis(
    proof: &Proof,
    proof_heap: &QueryHeap,
    dst: &mut QueryHeap,
    predicate_table: &PredicateTable,
) -> (SmallH, Vec<PredDef>) {
    let mut ref_map = HashMap::new();

    let mut meta_subs: Vec<MetaSub> = proof
        .hypothesis
        .meta_subs
        .iter()
        .map(|meta_sub| clone_meta_sub(dst, proof_heap, meta_sub, &mut ref_map))
        .collect();

    let pred_defs = PredDef::extract_pred_defs_from_h(&mut meta_subs, predicate_table, dst);
    // Collected, not `into()`: converting a `Vec` keeps its heap buffer.
    (meta_subs.into_iter().collect(), pred_defs)
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
        VarId(var_id) => proof_heap.var_deref(var_id),
        bound @ Addr(_) => bound,
    };
    match resolved {
        Addr(addr) => {
            let new_addr = dst.heap_len();
            dst.clone_term_from_other(proof_heap, addr, ref_map);
            VarReg::from_addr(new_addr)
        }
        VarId(var_id) => {
            let new_var_id = *ref_map
                .entry(var_id)
                .or_insert_with(|| dst.new_var(VarReg::UNBOUND));
            VarReg::from_var(new_var_id)
        }
    }
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
    use crate::heap::test_prog;
    use crate::heap::{Heap, Tag::Con};
    use smallvec::smallvec;

    /// Build a `Proof` with no goals (so it never actually resolves anything)
    /// whose hypothesis holds `meta_subs`. Good enough to exercise
    /// [`extract_hypothesis`], which only ever reads those.
    fn proof_with_hypothesis<'a>(proof_heap: &QueryHeap, meta_subs: Vec<MetaSub>) -> Proof<'a> {
        let mut proof = Proof::new(proof_heap, &[]);
        proof.hypothesis.meta_subs = meta_subs;
        proof
    }

    /// A program heap holding the meta rule `P(X,Y):-Q(X,Y)`, the table to
    /// look it up in, and its id. Its substitutions are `[P, Q]`.
    fn prog_with_meta_rule() -> (ProgramHeap, PredicateTable, usize) {
        let mut prog = ProgramHeap::new();
        let meta = crate::parser::_build_clause(&mut prog, "P(X,Y):-Q(X,Y),{P,Q}.");
        let id = meta.meta_data.unwrap().id;
        let mut table = PredicateTable::new();
        let symbol_arity = prog.symbol_arity(meta.head());
        table.add_clause_to_predicate(meta, symbol_arity).unwrap();
        (prog, table, id)
    }

    #[test]
    fn clone_var_reg_reuses_ref_map_for_repeated_unbound_variable() {
        let prog = test_prog();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let v = proof_heap.new_var(VarReg::UNBOUND);
        let mut dst = QueryHeap::detached(&prog);
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
        let prog = test_prog();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let sym = prog.symbols().set_const("q");
        let addr_q = proof_heap.heap_push((Con, sym));

        let mut dst = QueryHeap::detached(&prog);
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
        let prog = test_prog();
        // Simulates a MetaSub recorded while an arg register was still an
        // unbound variable, with the proof later binding that variable to an
        // address before extraction runs.
        let mut proof_heap = QueryHeap::new(&prog, None);
        let sym = prog.symbols().set_const("p");
        let addr_p = proof_heap.heap_push((Con, sym));
        let v = proof_heap.new_var(VarReg::UNBOUND);
        proof_heap.bind(v, Addr(addr_p));

        let mut dst = QueryHeap::detached(&prog);
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
        let prog = test_prog();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let v1 = proof_heap.new_var(VarReg::UNBOUND);
        let v2 = proof_heap.new_var(VarReg::UNBOUND);
        let meta_sub = MetaSub {
            meta_clause_id: 7,
            subs: smallvec![VarReg::from_var(v1), VarReg::from_var(v2)],
        };

        let mut dst = QueryHeap::detached(&prog);
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
    fn extract_hypothesis_keeps_constant_headed_clauses() {
        // `p(X,Y):-q(X,Y)` and `p(X,Y):-Var(X,Y)`: neither head is a
        // predicate variable, so neither is lifted -- not even the second,
        // whose only predicate variable is in its body.
        let (prog, table, meta_clause_id) = prog_with_meta_rule();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let p = proof_heap.heap_push((Con, prog.symbols().set_const("p")));
        let q = proof_heap.heap_push((Con, prog.symbols().set_const("q")));
        let body_var = proof_heap.new_var(VarReg::UNBOUND);
        let meta_subs = vec![
            MetaSub {
                meta_clause_id,
                subs: smallvec![VarReg::from_addr(p), VarReg::from_addr(q)],
            },
            MetaSub {
                meta_clause_id,
                subs: smallvec![VarReg::from_addr(p), VarReg::from_var(body_var)],
            },
        ];

        let proof = proof_with_hypothesis(&proof_heap, meta_subs);
        let mut dst = QueryHeap::detached(&prog);
        let (hypothesis, pred_defs) = extract_hypothesis(&proof, &proof_heap, &mut dst, &table);

        assert!(pred_defs.is_empty());
        assert_eq!(hypothesis.len(), 2);
        assert_eq!(hypothesis[0].meta_clause_id, meta_clause_id);
        // Only the three constant substitution terms land on `dst`.
        assert_eq!(dst.cells.len(), 3);
    }

    #[test]
    fn extract_hypothesis_lifts_predicate_variable_headed_clauses() {
        // `Var(X,Y):-Var(X,Y)` -- the head predicate is a variable, so the
        // clause is lifted into a PredDef, and the variable repeated in its
        // MetaSub must land on a single destination variable (the shared
        // `ref_map`).
        let (prog, table, meta_clause_id) = prog_with_meta_rule();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let pred_var = proof_heap.new_var(VarReg::UNBOUND);
        let meta_sub = MetaSub {
            meta_clause_id,
            subs: smallvec![VarReg::from_var(pred_var), VarReg::from_var(pred_var)],
        };

        let proof = proof_with_hypothesis(&proof_heap, vec![meta_sub]);
        let mut dst = QueryHeap::detached(&prog);
        let (hypothesis, pred_defs) = extract_hypothesis(&proof, &proof_heap, &mut dst, &table);

        assert!(
            hypothesis.is_empty(),
            "a predicate-variable-headed clause should be lifted into a PredDef"
        );
        assert_eq!(pred_defs.len(), 1);
        assert_eq!(pred_defs[0].meta_subs.len(), 1);

        let subs = &pred_defs[0].meta_subs[0].subs;
        assert_eq!(subs.len(), 2);
        assert!(subs[0].var(), "an unbound predicate clones to a variable");
        assert_eq!(
            subs[0], subs[1],
            "repeated occurrences of one proof variable must share one \
             destination variable"
        );
    }

    #[test]
    fn extract_hypothesis_uses_a_fresh_ref_map_each_call() {
        // Two "solutions" of the same proof can legitimately reuse the same
        // proof-heap var id (backtracking resets and reassigns registers).
        // Each call to `extract_hypothesis` must still land on a distinct
        // destination variable rather than aliasing the two solutions.
        let (prog, table, meta_clause_id) = prog_with_meta_rule();
        let mut proof_heap = QueryHeap::new(&prog, None);
        let pred_var = proof_heap.new_var(VarReg::UNBOUND);
        let q = proof_heap.heap_push((Con, prog.symbols().set_const("q")));
        let meta_sub = MetaSub {
            meta_clause_id,
            subs: smallvec![VarReg::from_var(pred_var), VarReg::from_addr(q)],
        };

        let mut dst = QueryHeap::detached(&prog);

        let proof1 = proof_with_hypothesis(&proof_heap, vec![meta_sub.clone()]);
        let (_, pred_defs1) = extract_hypothesis(&proof1, &proof_heap, &mut dst, &table);

        let proof2 = proof_with_hypothesis(&proof_heap, vec![meta_sub]);
        let (_, pred_defs2) = extract_hypothesis(&proof2, &proof_heap, &mut dst, &table);

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
    use crate::heap::test_prog;
    use crate::heap::Tag::{Comp, Con};
    use smallvec::smallvec;

    /// [`merge_thread_results`] with the progress-reporting arguments filled
    /// in: these tests supply every message up front, so the number of
    /// examples searched is simply the message count.
    fn merge(
        results: Vec<ThreadResult>,
        heap: &ProgramHeap,
    ) -> (Vec<Cell>, PackedMetaSubs, PredDefTable) {
        let total = results.len();
        merge_thread_results(results, heap, total, &AtomicUsize::new(total))
    }

    /// A fresh, 0-indexed thread-local heap to build a test's clauses and
    /// predicate definitions against.

    fn thread_heap() -> QueryHeap<'static> {
        QueryHeap::new(test_prog(), None)
    }

    /// Deconstruct a per-hypothesis heap into the `(cells, var_regs)` pair
    /// `generalise_thread` actually sends.
    fn parts(heap: QueryHeap<'static>) -> (Vec<Cell>, Vec<VarReg>) {
        (heap.cells, heap.var_regs)
    }

    #[test]
    fn merge_grounds_a_pred_defs_variable() {
        let mut heap = thread_heap();
        let pred_var = heap.new_var(VarReg::UNBOUND);
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: smallvec![VarReg::from_var(pred_var)],
        };
        let pred_def = PredDef::new(smallvec![meta_sub]);

        let (cells, hypotheses, pdt) = merge(
            vec![(SmallVec::new(), vec![pred_def], parts(heap))],
            test_prog(),
        );

        assert_eq!(hypotheses.len(), 0);
        // The only cell is the constant coined for the predicate.
        assert_eq!(cells.len(), 1);
        assert_eq!(cells[0].0, Con);

        assert_eq!(pdt.len(), 1);
        assert_eq!(pdt.get(0).get(0).subs().nth(0).unwrap(), VarReg::from_addr(0));
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
            heap.heap_push((Var, pred_var));
            let meta_sub = MetaSub {
                meta_clause_id,
                subs: smallvec![VarReg::from_var(pred_var)],
            };
            let pred_def = PredDef::new(smallvec![meta_sub]);
            (SmallVec::new(), vec![pred_def], parts(heap))
        };

        let (cells, hypotheses, pdt) = merge(vec![make_message(0), make_message(1)], test_prog());

        assert_eq!(hypotheses.len(), 0);
        assert_eq!(
            pdt.len(),
            2,
            "distinct meta_clause_ids should not unify together"
        );
        for (i, cell) in cells.iter().enumerate() {
            assert_ne!(cell.0, Var, "cell {i} ({cell:?}) should have been grounded");
        }

        // Each message coined its own fresh constant; they must not alias.
        let (first_const_addr, _) = pdt.get(0).get(0).subs().nth(0).unwrap()
            .get_bind()
            .and_then(|b| if let Addr(a) = b { Some((a, ())) } else { None })
            .expect("first pred_def's binding should be a resolved address");
        let (second_const_addr, _) = pdt.get(1).get(0).subs().nth(0).unwrap()
            .get_bind()
            .and_then(|b| if let Addr(a) = b { Some((a, ())) } else { None })
            .expect("second pred_def's binding should be a resolved address");
        assert_ne!(cells[first_const_addr], cells[second_const_addr]);
    }

    #[test]
    fn merge_shifts_substitution_addresses_between_messages() {
        let prog = test_prog();
        let sym_p = prog.symbols().set_const("merge_test_shift_p");
        let sym_q = prog.symbols().set_const("merge_test_shift_q");

        let message = |sym: usize| {
            let mut heap = thread_heap();
            let addr = heap.heap_push((Con, sym));
            let meta_sub = MetaSub {
                meta_clause_id: 0,
                subs: smallvec![VarReg::from_addr(addr)],
            };
            (smallvec![meta_sub], Vec::new(), parts(heap))
        };

        let (cells, hypotheses, _) = merge(vec![message(sym_p), message(sym_q)], test_prog());

        assert_eq!(cells, vec![(Con, sym_p), (Con, sym_q)]);
        assert_eq!(
            hypotheses.len(),
            2,
            "different constants are different hypotheses"
        );
        assert_eq!(
            hypotheses.get(0).get(0).subs().nth(0).unwrap(),
            VarReg::from_addr(0),
            "first message is not shifted"
        );
        assert_eq!(
            hypotheses.get(1).get(0).subs().nth(0).unwrap(),
            VarReg::from_addr(1),
            "second message's substitution should be shifted past the first message's cells"
        );
    }

    #[test]
    fn merge_drops_duplicate_hypotheses_found_across_messages() {
        let prog = test_prog();
        let sym_p = prog.symbols().set_const("merge_test_dup_p");

        let message = || {
            let mut heap = thread_heap();
            let addr = heap.heap_push((Con, sym_p));
            let meta_sub = MetaSub {
                meta_clause_id: 0,
                subs: smallvec![VarReg::from_addr(addr)],
            };
            (smallvec![meta_sub], Vec::new(), parts(heap))
        };

        let (cells, hypotheses, _) = merge(vec![message(), message()], test_prog());

        assert_eq!(
            hypotheses.len(),
            1,
            "the second message's identical hypothesis should be deduplicated"
        );
        // The duplicate's term is found in the index, not copied again.
        assert_eq!(cells.len(), 1);
    }

    #[test]
    fn merge_stores_a_term_named_by_several_messages_once() {
        let prog = test_prog();
        let sym_p = prog.symbols().set_const("merge_test_share_p");

        // Different meta clauses, so the hypotheses differ, but the same
        // constant.
        let message = |meta_clause_id: usize| {
            let mut heap = thread_heap();
            let addr = heap.heap_push((Con, sym_p));
            let meta_sub = MetaSub {
                meta_clause_id,
                subs: smallvec![VarReg::from_addr(addr)],
            };
            (smallvec![meta_sub], Vec::new(), parts(heap))
        };

        let (cells, hypotheses, _) = merge(vec![message(0), message(1)], test_prog());

        assert_eq!(cells, vec![(Con, sym_p)]);
        assert_eq!(hypotheses.len(), 2);
        assert_eq!(hypotheses.get(0).get(0).subs().nth(0).unwrap(), hypotheses.get(1).get(0).subs().nth(0).unwrap());
    }

    #[test]
    fn merge_reuses_a_constant_inside_an_earlier_compound_term() {
        let prog = test_prog();
        let sym_f = prog.symbols().set_const("merge_test_sub_f");
        let sym_a = prog.symbols().set_const("merge_test_sub_a");

        // `f(a)`, then `a` on its own.
        let mut compound = thread_heap();
        let f_a = compound.heap_push((Comp, 2));
        compound.heap_push((Con, sym_f));
        compound.heap_push((Con, sym_a));
        let first = MetaSub {
            meta_clause_id: 0,
            subs: smallvec![VarReg::from_addr(f_a)],
        };

        let mut constant = thread_heap();
        let a = constant.heap_push((Con, sym_a));
        let second = MetaSub {
            meta_clause_id: 0,
            subs: smallvec![VarReg::from_addr(a)],
        };

        let (cells, hypotheses, _) = merge(
            vec![
                (smallvec![first], Vec::new(), parts(compound)),
                (smallvec![second], Vec::new(), parts(constant)),
            ],
            test_prog(),
        );

        assert_eq!(cells, vec![(Comp, 2), (Con, sym_f), (Con, sym_a)]);
        assert_eq!(hypotheses.len(), 2);
        assert_eq!(
            hypotheses.get(1).get(0).subs().nth(0).unwrap(),
            VarReg::from_addr(2),
            "`a` should reuse the argument cell of `f(a)`"
        );
    }

    #[test]
    #[should_panic(expected = "Not all variable predicates given constant terms")]
    fn merge_panics_if_a_ref_cell_survives_grounding() {
        // A term holding a variable that no pred_def grounds must trip the
        // same guard `App::run_top_prog` relies on never firing.
        let prog = test_prog();
        let sym_f = prog.symbols().set_const("merge_test_stray_f");
        let mut heap = thread_heap();
        let stray_var = heap.new_var(VarReg::UNBOUND);
        let term = heap.heap_push((Comp, 2));
        heap.heap_push((Con, sym_f));
        heap.heap_push((Var, stray_var));
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: smallvec![VarReg::from_addr(term)],
        };

        let _ = merge(vec![(smallvec![meta_sub], Vec::new(), parts(heap))], test_prog());
    }

    #[test]
    #[should_panic(expected = "Not all variable predicates given constant terms")]
    fn merge_panics_if_a_hypothesis_stays_unbound() {
        // A hypothesis variable still unbound after the definition inserts
        // names an invented predicate that nothing defined.
        let mut heap = thread_heap();
        let stray_var = heap.new_var(VarReg::UNBOUND);
        let meta_sub = MetaSub {
            meta_clause_id: 0,
            subs: smallvec![VarReg::from_var(stray_var)],
        };

        let _ = merge(vec![(smallvec![meta_sub], Vec::new(), parts(heap))], test_prog());
    }
}
