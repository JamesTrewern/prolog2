//! Rejecting candidates that entail a negative example.
//!
//! Specialisation is no longer a pass of its own. Each worker applies
//! [`hypothesis_entails_negative`] to a sub hypothesis the moment the search
//! finds it, so nothing that proves a negative is ever collected, and
//! [`clauses_entail_negative`] is applied again later to whole *combinations*
//! of sub hypotheses -- two that are each consistent can together entail a
//! negative, since a clause from one can resolve against a clause from the
//! other.
//!
//! Both answer the same question and both report it the same way round:
//! `true` means a negative is provable, so the candidate must go.

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::RwLock,
};

use crate::{
    heap::{
        Cell, Heap, QueryHeap, SymbolDB,
        Tag::{Con, Var},
        TermWalk, Walk,
    },
    program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::Proof,
    Config,
};
use lazy_static::lazy_static;
use rayon::prelude::*;

/// Most distinct predicate variables one hypothesis can hold.
const MAX_INVENTED: usize = 64;

lazy_static! {
    /// Constants standing in for a hypothesis's predicate variables while it
    /// is tested against the negatives.
    ///
    /// Interned once. Minting them per candidate would take the symbol
    /// table's write lock on every one of them, which at this volume is
    /// itself a bottleneck. The `$` prefix keeps them clear of the `pred_N`
    /// constants the predicate definition table coins, which name real
    /// predicates and would otherwise collide.
    static ref INVENTED_SYMBOLS: Vec<usize> = (0..MAX_INVENTED)
        .map(|i| SymbolDB::set_const(format!("$inv_{i}")))
        .collect();
}

/// Learning disabled, so a negative is tested against the candidate rather
/// than extended into a new hypothesis. `max_depth` is kept to bound
/// recursive candidates.
fn test_config(config: Config) -> Config {
    Config {
        max_depth: config.max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    }
}

/// Does this set of ground clauses prove any negative example?
///
/// For candidates whose invented predicates have already been coined as
/// constants, which can be proved on a heap of their own. `neg_goals` are
/// addresses of goals compiled onto `heap` by
/// [`compile_examples`](super::utils::compile_examples).
///
/// `par_iter().any()` abandons the remaining negatives as soon as one is
/// proved.
pub(super) fn clauses_entail_negative(
    neg_goals: &[usize],
    clauses: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
) -> bool {
    let config = test_config(config);

    neg_goals.into_par_iter().any(|&goal| {
        let mut query_heap = QueryHeap::new(heap, None);
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(clauses);
        proof.prove(&mut query_heap, predicate_table, config)
    })
}

/// Verdicts already reached, shared by every worker.
/// Sharded rather than held behind one lock: at well over a million lookups
/// a single mutex would serialise the workers it is meant to be saving.
pub(super) struct NegativeCache {
    shards: Vec<RwLock<HashMap<u128, bool>>>,
    hits: std::sync::atomic::AtomicUsize,
    misses: std::sync::atomic::AtomicUsize,
}

const CACHE_SHARDS: usize = 64;

impl NegativeCache {
    pub(super) fn new() -> Self {
        Self {
            shards: (0..CACHE_SHARDS)
                .map(|_| RwLock::new(HashMap::new()))
                .collect(),
            hits: std::sync::atomic::AtomicUsize::new(0),
            misses: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    fn shard(&self, key: u128) -> &RwLock<HashMap<u128, bool>> {
        &self.shards[(key % CACHE_SHARDS as u128) as usize]
    }

    /// The verdict already reached for `key`, if any.
    fn get(&self, key: u128) -> Option<bool> {
        use std::sync::atomic::Ordering::Relaxed;

        let cached = self.shard(key).read().unwrap().get(&key).copied();
        if cached.is_some() {
            self.hits.fetch_add(1, Relaxed);
        }
        cached
    }

    /// Record a verdict reached by running the proofs.
    ///
    /// No lock is held while those proofs run, so two workers reaching the
    /// same unseen hypothesis at once both test it and both store the same
    /// answer. Doing that work twice is cheaper than holding a shard closed
    /// for the length of a proof.
    fn record(&self, key: u128, verdict: bool) {
        use std::sync::atomic::Ordering::Relaxed;
        self.misses.fetch_add(1, Relaxed);
        self.shard(key).write().unwrap().insert(key, verdict);
    }

    /// `(hits, misses, distinct hypotheses stored)`
    pub(super) fn stats(&self) -> (usize, usize, usize) {
        use std::sync::atomic::Ordering::Relaxed;
        let stored = self.shards.iter().map(|s| s.read().unwrap().len()).sum();
        (self.hits.load(Relaxed), self.misses.load(Relaxed), stored)
    }
}

/// A fingerprint identifying this hypothesis up to renaming of its predicate
/// variables.
///
/// Walks the same flattened cells [`ground_hypothesis`] would copy, numbering
/// predicate variables by first appearance, so two hypotheses that differ
/// only in which variable ids they happened to be given hash alike. Nothing
/// is allocated and no term is rendered: at this volume building strings to
/// compare would cost more than the proofs being saved.
///
/// Two independent hashes are combined into 128 bits. A collision would hand
/// one hypothesis another's verdict, and at over a million entries 64 bits
/// leaves more room for that than is comfortable.
fn hypothesis_key(heap: &QueryHeap, hypothesis: &Hypothesis) -> u128 {
    use std::collections::hash_map::DefaultHasher;

    let mut low = DefaultHasher::new();
    let mut high = DefaultHasher::new();
    0x9E37_79B9_7F4A_7C15u64.hash(&mut high);

    let mut seen: HashMap<usize, usize> = HashMap::new();
    for clause in hypothesis.iter() {
        for &literal in clause.iter() {
            // Separator, so the same cells split differently across literals
            // cannot collide.
            u8::MAX.hash(&mut low);
            u8::MAX.hash(&mut high);

            let mut walk = TermWalk::new(literal);
            while let Some((tag, value)) = walk.next_cell(heap) {
                let (tag, value) = if tag == Var {
                    let next = seen.len();
                    (u8::MAX, *seen.entry(value).or_insert(next))
                } else {
                    (tag as u8, value)
                };
                (tag, value).hash(&mut low);
                (tag, value).hash(&mut high);
            }
        }
    }

    ((low.finish() as u128) << 64) | high.finish() as u128
}

/// Copy `hypothesis`'s clauses onto `heap`, replacing every predicate
/// variable with a constant.
///
/// A predicate variable left as a variable would have to be protected, by
/// the invented-predicate registry and the constraint set, from resolving
/// against a background fact and collapsing the invention. Giving it a
/// constant of its own enforces the same thing structurally -- nothing else
/// in the program carries that symbol -- so the test proofs need neither
/// mechanism.
///
/// It also leaves the clauses completely ground, which is what lets the
/// branches below start with no variable registers at all: with no `Var`
/// cell left to dereference, a branch never consults its parent's.
///
/// Appends to `heap`; the caller truncates.
fn ground_hypothesis(heap: &mut QueryHeap, hypothesis: &Hypothesis) -> Vec<Clause> {
    let mut consts: HashMap<usize, usize> = HashMap::new();

    hypothesis
        .iter()
        .map(|clause| {
            let literals: Vec<usize> = clause
                .iter()
                .map(|&literal| {
                    let new_addr = heap.heap_len();
                    let mut walk = TermWalk::new(literal);
                    // `next_cell` resolves as it goes: a bound variable is
                    // replaced by the term it names, and an unbound one comes
                    // back as its representative, so each distinct predicate
                    // variable is seen under one id however it was aliased.
                    while let Some(cell) = walk.next_cell(heap) {
                        if let (Var, var_id) = cell {
                            let next = consts.len();
                            assert!(
                                next < MAX_INVENTED,
                                "hypothesis holds more than {MAX_INVENTED} predicate variables"
                            );
                            let symbol = *consts.entry(var_id).or_insert(INVENTED_SYMBOLS[next]);
                            heap.heap_push((Con, symbol));
                        } else {
                            heap.heap_push(cell);
                        }
                    }
                    new_addr
                })
                .collect();
            Clause::new(literals, None, clause.max_arg_id)
        })
        .collect()
}

/// What a worker should do with a candidate it has just found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Verdict {
    /// Proves a negative example; drop it.
    EntailsNegative,
    /// Consistent with the negatives, and the first of its kind: collect it.
    Keep,
    /// Consistent, but another worker got to an identical hypothesis first,
    /// so it has already been collected and this copy is redundant.
    ///
    /// Workers searching different positive examples rediscover the same
    /// hypothesis constantly, and extracting it again would clone its terms
    /// into the thread's heap and push its invented predicates through the
    /// definition table for a second time, only for the merge to throw the
    /// duplicate away at the end.
    AlreadyFound,
}

/// Decide what to do with a candidate: test it against the negatives, or
/// reuse the verdict another worker already reached for the same hypothesis.
///
/// Whether a hypothesis entails a negative depends only on the hypothesis and
/// the negatives, never on which positive example led to it, so a verdict is
/// shared safely across workers.
///
/// Below: does this hypothesis, still mid-search, prove any negative example?
///
/// Each negative gets its own [branch](QueryHeap::branch) of the search heap:
/// a heap that reads the program cells and everything the search has built --
/// including the hypothesis clause literals, which exist nowhere else -- but
/// writes only its own cells and its own copy of the variable registers. The
/// branches are therefore independent, so the negatives run in parallel and
/// `any` abandons the rest the moment one is proved.
///
/// Nothing needs undoing afterwards. A branch cannot touch its parent's cells
/// (`IndexMut` refuses them) and binds only its copied registers, so dropping
/// it restores the search heap by construction.
///
/// [`Proof::with_hypothesis`] clones the whole hypothesis, so the inner proof
/// inherits the constraint set and the invented-predicate registry. That
/// matters here and not in [`clauses_entail_negative`]: the invented
/// predicates are still unbound variables at this point, and without the
/// registry a goal on one would resolve against a background fact and
/// collapse the invention, failing a negative the real hypothesis does not
/// entail.
pub(super) fn specialise_candidate(
    neg_goals: &[usize],
    hypothesis: &Hypothesis,
    heap: &mut QueryHeap,
    predicate_table: &PredicateTable,
    config: Config,
    cache: &NegativeCache,
) -> Verdict {
    let key = hypothesis_key(heap, hypothesis);
    if let Some(entailed) = cache.get(key) {
        return if entailed {
            Verdict::EntailsNegative
        } else {
            Verdict::AlreadyFound
        };
    }

    // No negatives: nothing to prove, but the key was still worth taking --
    // it is what tells the other workers this one is already collected.
    if neg_goals.is_empty() {
        cache.record(key, false);
        return Verdict::Keep;
    }

    // Nothing is left to protect once the predicate variables are constants.
    let config = Config {
        protect_h_preds: false,
        ..test_config(config)
    };

    let point = heap.heap_point();
    let grounded = ground_hypothesis(heap, hypothesis);

    let mut branches = heap.branch(neg_goals.len());
    let entailed = branches
        .par_iter_mut()
        .zip(neg_goals.par_iter())
        .any(|(branch, &goal)| {
            let mut inner = Proof::new(branch, &[goal]);
            inner.add_test_clauses(&grounded);
            inner.prove(branch, predicate_table, config)
        });

    drop(branches);
    heap.truncate(point);

    cache.record(key, entailed);
    if entailed {
        Verdict::EntailsNegative
    } else {
        Verdict::Keep
    }
}
