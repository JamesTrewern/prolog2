use std::{
    cmp::Ordering::{self, *},
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

use smallvec::SmallVec;

use crate::{
    heap::{
        Heap, QueryHeap,
        Tag::*,
        VarBind::{self, Addr, VarId},
        VarReg,
    },
    program::{MetaSub, MetaSubGroup, MetaSubTrait, PackedMetaSubs, PredicateTable},
    utils::{DirGraph16, DirGraph8},
    PRED_DEF_DEFAULT_SIZE,
};

/// Most invented predicates one sub hypothesis can define.
///
/// Set by the widest dependency graph available
/// ([`DirGraph16`](crate::utils::DirGraph16)). A hypothesis cannot invent
/// more predicates than it has clauses, so bounding `max_clause` by this
/// bounds the number of clause sets too.
pub(super) const MAX_PRED_DEFS: usize = 16;

#[derive(Debug)]
pub(super) struct PredDef {
    /// Sorted by `clause_idx`.
    pub meta_subs: SmallVec<[MetaSub; PRED_DEF_DEFAULT_SIZE]>,
}

impl Deref for PredDef {
    type Target = [MetaSub];
    fn deref(&self) -> &Self::Target {
        &self.meta_subs
    }
}
impl DerefMut for PredDef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta_subs
    }
}

impl PredDef {
    /// Take clauses to form new predicate definition (orders clauses)
    pub(super) fn new(mut meta_subs: SmallVec<[MetaSub; PRED_DEF_DEFAULT_SIZE]>) -> Self {
        meta_subs.sort_by_key(|meta_sub| meta_sub.clause_idx);
        Self { meta_subs }
    }

    /// Ground every substitution in this definition, coining a fresh constant
    /// for the predicate it defines.
    ///
    /// Only the first substitution of each `MetaSub` can need a new constant.
    /// That position is the functor of the clause head -- the predicate this
    /// definition defines -- and it is the only variable the definition itself
    /// introduces. Every other position is a body predicate, and a definition
    /// is only inserted once the definitions it depends on are already in the
    /// table (see [`Self::extract_pred_defs_from_h`], which orders them), so
    /// by now those are bound to the constants coined for *their* heads.
    ///
    /// Body positions are still rewritten from `Var` to the address they
    /// dereference to. Leaving them as variable registers would strand them:
    /// the merge loop resets its variable window after each worker result, so
    /// a stored `Var` would later read back unbound and unify with anything.
    ///
    /// An unbound body position means a definition reached the table before
    /// the one it depends on, which the debug assertion below reports rather
    /// than papering over by coining a constant for a predicate that already
    /// has one.
    pub(super) fn make_const(&mut self, heap: &mut impl Heap) {
        // Heads first, across every clause. A mutually recursive group is
        // collected into a single definition, so one clause's body predicate
        // may be the head of a *later* clause in this same definition; coining
        // clause by clause would meet that body before its head.
        for meta_sub in self.iter_mut() {
            let Some(head) = meta_sub.subs.first_mut() else {
                continue;
            };
            if let Some(VarId(var_id)) = head.get_bind() {
                match heap.var_deref(var_id) {
                    // Already coined -- by an earlier clause of this same
                    // definition, or by unification against the table.
                    bound @ Addr(_) => *head = bound.into(),
                    VarId(var_id) => {
                        let pred_symbol = heap.symbols().next_inv();
                        let addr = heap.heap_push((Con, pred_symbol));
                        heap.bind(var_id, Addr(addr));
                        *head = Addr(addr).into();
                    }
                }
            }
        }

        for meta_sub in self.iter_mut() {
            for var_reg in meta_sub.subs.iter_mut().skip(1) {
                if let Some(VarId(var_id)) = var_reg.get_bind() {
                    let bound = heap.var_deref(var_id);
                    debug_assert!(
                        matches!(bound, Addr(_)),
                        "body predicate variable {var_id} is still unbound while grounding the \
                         definition that uses it: it is neither defined by this definition nor \
                         already in the table, so the two were inserted in the wrong order"
                    );
                    *var_reg = bound.into();
                }
            }
        }
    }

    /// Lift the clauses that define an invented predicate out of a
    /// hypothesis into dependency-ordered definitions, leaving the rest of
    /// the hypothesis behind in `meta_subs`.
    ///
    /// Works from the substitutions alone: each meta clause records which of
    /// its meta variables are in predicate positions, so a clause defines an
    /// invented predicate when its head predicate is still a variable, and
    /// depends on the body predicates that are. `heap` is the heap the
    /// substitutions' variables live on.
    pub(super) fn extract_pred_defs_from_h(
        meta_subs: &mut Vec<MetaSub>,
        predicate_table: &PredicateTable,
        heap: &impl Heap,
    ) -> Vec<Self> {
        /// The predicate variable a substitution names, if it still names one.
        fn pred_var(meta_sub: &MetaSub, sub_idx: usize, heap: &impl Heap) -> Option<usize> {
            match meta_sub.subs.get(sub_idx)?.get_bind()? {
                VarId(var_id) => match heap.var_deref(var_id) {
                    VarId(var_id) => Some(var_id),
                    Addr(_) => None,
                },
                Addr(_) => None,
            }
        }

        let mut clause_sets: Vec<SmallVec<[MetaSub; PRED_DEF_DEFAULT_SIZE]>> =
            Vec::with_capacity(meta_subs.len());
        let mut var_preds = Vec::with_capacity(meta_subs.len());
        let mut dependencies: Vec<HashSet<usize>> = Vec::with_capacity(meta_subs.len());

        for idx in (0..meta_subs.len()).rev() {
            let meta_clause = meta_subs[idx].template(predicate_table);
            let Some(var_id) = meta_clause
                .head_pred_sub_index()
                .and_then(|head_idx| pred_var(&meta_subs[idx], head_idx, heap))
            else {
                continue;
            };

            let body_var_preds = meta_clause
                .body_pred_sub_indices()
                .filter_map(|sub_idx| pred_var(&meta_subs[idx], sub_idx, heap));
            let def_index = match var_preds.iter().position(|var_pred| *var_pred == var_id) {
                Some(def_index) => def_index,
                None => {
                    var_preds.push(var_id);
                    dependencies.push(HashSet::new());
                    clause_sets.push(SmallVec::new());
                    var_preds.len() - 1
                }
            };
            dependencies[def_index].extend(body_var_preds);
            clause_sets[def_index].push(meta_subs.remove(idx));
        }

        // Each clause set is one invented predicate, so there are never more
        // of them than there are clauses in the hypothesis, and `run_top_prog`
        // refuses a `max_clause` above `MAX_PRED_DEFS`.
        let node_of = |dep: usize| {
            var_preds
                .iter()
                .position(|var_pred| *var_pred == dep)
                .expect("every body predicate variable also heads a clause set")
        };

        let groups: Vec<u64> = match clause_sets.len() {
            n if n <= 8 => {
                let mut graph = DirGraph8::new(n);
                for (i, deps) in dependencies.iter().enumerate() {
                    for &dep in deps {
                        graph.add_edge(i, node_of(dep));
                    }
                }
                match graph.ordered_cyclic_groups() {
                    Some(groups) => groups[..groups.size].iter().map(|&g| g as u64).collect(),
                    None => graph.order()[..graph.size]
                        .iter()
                        .map(|&i| 1 << i)
                        .collect(),
                }
            }
            n if n <= MAX_PRED_DEFS => {
                let mut graph = DirGraph16::new(n);
                for (i, deps) in dependencies.iter().enumerate() {
                    for &dep in deps {
                        graph.add_edge(i, node_of(dep));
                    }
                }
                match graph.ordered_cyclic_groups() {
                    Some(groups) => groups[..groups.size].iter().map(|&g| g as u64).collect(),
                    None => graph.order()[..graph.size]
                        .iter()
                        .map(|&i| 1 << i)
                        .collect(),
                }
            }
            n => unreachable!(
                "{n} invented predicates in one sub hypothesis exceeds the {MAX_PRED_DEFS} \
                 the dependency graph can hold; a hypothesis cannot have more invented \
                 predicates than clauses, and max_clause is checked against this limit \
                 before the search starts"
            ),
        };

        // A group is a set of mutually dependent predicates, which have to be
        // defined together; the acyclic path above hands back one singleton
        // per predicate so both cases assemble the same way.
        groups
            .into_iter()
            .map(|group| {
                let mut meta_subs: SmallVec<[MetaSub; PRED_DEF_DEFAULT_SIZE]> = SmallVec::new();
                for (i, clause_set) in clause_sets.iter_mut().enumerate() {
                    if group & 1 << i != 0 {
                        meta_subs.extend(clause_set.drain(..));
                    }
                }
                PredDef::new(meta_subs)
            })
            .collect()
    }
}

/// A predicate definition: clauses sorted by meta clause id.
///
/// Implemented by the owned [`PredDef`] a worker sends and by the
/// [`PredDefRef`] view of one stored in a [`PredDefTable`], so the two are
/// compared without converting either.
pub(super) trait PredDefLike {
    type Sub: MetaSubTrait + ?Sized;

    fn clause_count(&self) -> usize;

    fn clause(&self, index: usize) -> &Self::Sub;

    fn clauses(&self) -> impl Iterator<Item = &Self::Sub> {
        (0..self.clause_count()).map(|index| self.clause(index))
    }

    /// Attempt to unify two clause definitions
    /// Self should be constant
    /// will update variable bindings on heap effecting other variable clause defintions waiting to unify
    fn unify<O: PredDefLike>(&self, other: &O, heap: &mut QueryHeap) -> bool {
        // TODO consider if different meta_rules might result in the same clause
        if self.signature_cmp(other) != Equal {
            return false;
        }
        let mut stack: Vec<(usize, Vec<usize>)> = Vec::new(); // (last matched index, bindings)
        let mut unified = vec![false; self.clause_count()].into_boxed_slice();
        let mut i = 0;
        'outer: while i < other.clause_count() {
            // Fresh visit to this position: search from the start. A revisit
            // (backtrack) undoes the previous match at this position and
            // resumes the search just after it.
            let start = if i == stack.len() {
                stack.push((0, Vec::new()));
                0
            } else {
                let (last_j, bindings) = &stack[i];
                unified[*last_j] = false;
                heap.unbind(bindings);
                last_j + 1
            };

            //Attempt to find clause to unify with
            // Clauses are sorted by meta clause id, so skip the lower ids
            // and stop at the first higher one.
            let clause_idx = other.clause(i).clause_idx();
            for j in start..self.clause_count() {
                match self.clause(j).clause_idx().cmp(&clause_idx) {
                    Less => continue,
                    Greater => break,
                    Equal => {}
                }
                if unified[j] {
                    continue;
                }
                if let Some(binding) = self.clause(j).unify(other.clause(i), heap) {
                    unified[j] = true;
                    stack[i] = (j, binding);
                    i += 1;
                    continue 'outer;
                }
            }

            if i == 0 {
                return false;
            } else {
                stack.pop();
                i -= 1;
            }
        }

        true
    }

    /// Per-position canonical content profile, from which
    /// [`key_from_profile`] derives the bucket keys for definitions that
    /// could unify; `None` for a definition that cannot be keyed.
    ///
    /// Two definitions [`Self::unify`] would merge are identical except for
    /// the names of the predicates they define: the incoming one has unbound
    /// variables where the table entry has its coined constants. So the
    /// profile keeps everything unification requires to match -- meta clause
    /// ids and the ground terms' addresses -- and replaces the parts
    /// allowed to differ with the [`OWN`] marker on both sides.
    ///
    /// A position resolving to one of the definition's own heads is `Own`:
    /// before grounding that is an unbound in-group variable (the head of
    /// this clause, or of a mutually recursive sibling), after grounding the
    /// constant `make_const` coined for it. Both sides of a unifiable pair
    /// classify such a position `Own`, so recursive and mutually recursive
    /// groups key like any other definition.
    ///
    /// The one disagreement left is an *already ground* reference to a
    /// constant that happens to be the candidate entry's own head: the
    /// incoming side records its address, the entry `OWN`.
    /// [`PredDefTable::insert`] covers exactly that case by probing
    /// alternate keys with those addresses flipped to `OWN`.
    ///
    /// `None` is returned only when a position resolves to an unbound
    /// variable that heads no clause of this definition -- a dependency
    /// inserted out of order, which `make_const` separately asserts against.
    /// Such a definition takes the signature-scan fallback.
    ///
    /// Ground terms are keyed by address, so equal terms must share one
    /// address: the collector interns every term it is sent, and
    /// `make_const` coins each constant once. Two equal terms at different
    /// addresses would key apart and never be compared. Like any hash,
    /// equality of keys is necessary but not sufficient for unifiability --
    /// the caller confirms with [`Self::unify`].
    fn key_profile(&self, heap: &impl Heap) -> Option<KeyProfile> {
        let resolve = |var_reg: VarReg| match var_reg.get_bind() {
            Some(VarId(var_id)) => Some(heap.var_deref(var_id)),
            Some(bound @ Addr(_)) => Some(bound),
            None => None,
        };

        // The heads this definition defines, by resolved binding. In-group
        // references resolve to the *same* binding as the head they name --
        // the same unbound variable before grounding, the same address after
        // (`make_const` rewrites them through the shared variable) -- so
        // plain equality is exact.
        let mut own: SmallVec<[VarBind; PRED_DEF_DEFAULT_SIZE]> = SmallVec::new();
        for meta_sub in self.clauses() {
            if let Some(head) = meta_sub.subs().next() {
                own.push(resolve(head)?);
            }
        }

        let mut profile: KeyProfile = SmallVec::new();
        for meta_sub in self.clauses() {
            let mut positions: SmallVec<[usize; 4]> = SmallVec::new();
            for var_reg in meta_sub.subs() {
                let resolved = resolve(var_reg)?;
                positions.push(match resolved {
                    _ if own.contains(&resolved) => OWN,
                    Addr(addr) => addr,
                    // Unbound, and not a head of this definition: a missing
                    // dependency.
                    VarId(_) => return None,
                });
            }
            profile.push((meta_sub.clause_idx(), positions));
        }

        Some(profile)
    }

    /// Hash of the signature [`Self::signature_cmp`] orders by: clause count and meta
    /// clause ids. Groups every definition this one could conceivably unify
    /// with, for the fallback scan in [`PredDefTable::insert`].
    fn signature_key(&self) -> u64 {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        self.clause_count().hash(&mut hasher);
        for meta_sub in self.clauses() {
            meta_sub.clause_idx().hash(&mut hasher);
        }
        hasher.finish()
    }

    /// Order by clause count, then by meta clause ids.
    fn signature_cmp<O: PredDefLike>(&self, other: &O) -> Ordering {
        match self.clause_count().cmp(&other.clause_count()) {
            Equal => {
                for (msub1, msub2) in self.clauses().zip(other.clauses()) {
                    match msub1.clause_idx().cmp(&msub2.clause_idx()) {
                        Equal => continue,
                        ordering => return ordering,
                    }
                }
                Equal
            }
            ord => ord,
        }
    }
}

impl PredDefLike for PredDef {
    type Sub = MetaSub;

    fn clause_count(&self) -> usize {
        self.meta_subs.len()
    }

    fn clause(&self, index: usize) -> &MetaSub {
        &self.meta_subs[index]
    }
}

/// A definition stored in a [`PredDefTable`], read in place.
pub(super) type PredDefRef<'a> = MetaSubGroup<'a>;

impl PredDefLike for PredDefRef<'_> {
    type Sub = [usize];

    fn clause_count(&self) -> usize {
        self.len()
    }

    fn clause(&self, index: usize) -> &[usize] {
        self.get(index)
    }
}

/// Key of a position that resolves to one of the definition's own heads --
/// the predicate the clause defines, or an in-group reference to a mutually
/// recursive sibling. Unification is allowed to rename these, so they carry
/// no content. Every other position is keyed by its term's address.
const OWN: usize = usize::MAX;

/// `(clause_idx, position keys)` per clause, in `meta_subs` order.
pub(super) type KeyProfile = SmallVec<[(usize, SmallVec<[usize; 4]>); PRED_DEF_DEFAULT_SIZE]>;

/// Combine a [`KeyProfile`] into a bucket key, with the addresses in `flips`
/// reclassified as [`OWN`].
///
/// Clause order within a definition is free ([`PredDef::unify`] searches for
/// a pairing), so the per-clause vectors are sorted before the final combine,
/// making the key order-insensitive the same way. Sorting happens after the
/// flips are applied: the entry being probed for classified those positions
/// `OWN` before *its* sort, and the clause order has to be decided by the
/// same values on both sides.
pub(super) fn key_from_profile(profile: &KeyProfile, flips: &[usize]) -> u64 {
    use std::hash::{DefaultHasher, Hash, Hasher};

    let mut clauses: KeyProfile = profile
        .iter()
        .map(|(clause_idx, positions)| {
            let positions = positions
                .iter()
                .map(|pos| if flips.contains(pos) { OWN } else { *pos })
                .collect();
            (*clause_idx, positions)
        })
        .collect();
    clauses.sort_unstable();

    let mut hasher = DefaultHasher::new();
    clauses.hash(&mut hasher);
    hasher.finish()
}

#[derive(Default, Debug)]
pub(super) struct PredDefTable {
    /// Every definition, grounded, one group each.
    pred_defs: PackedMetaSubs,
    /// Symbol id of each constant coined to name a predicate defined here,
    /// mapped to the index of its definition; recorded as each definition
    /// is inserted.
    symbol_defs: HashMap<usize, u32>,
    /// [`PredDef::canonical_key`] of each grounded definition, mapped to its
    /// indices in `pred_defs`. Almost always a single index: two definitions
    /// share a key only on a genuine hash collision or when they differ in
    /// ways the key deliberately leaves out (set contents, the wiring of a
    /// mutually recursive group's own heads).
    buckets: HashMap<u64, SmallVec<[usize; 2]>>,
    /// [`PredDef::signature_key`] of each definition, mapped to its indices
    /// in `pred_defs`: every definition a given one could conceivably unify
    /// with, for incoming definitions `canonical_key` cannot key.
    signature_index: HashMap<u64, Vec<usize>>,
}

impl PredDefTable {
    /// Merge `pred_def` into an existing definition, or ground it and add it.
    ///
    /// A keyable definition (see [`PredDef::canonical_key`]) is matched
    /// against only the definitions in its key's bucket -- normally one or
    /// none. One that cannot be keyed (a mutually recursive group, still
    /// carrying unbound in-group references) falls back to scanning every
    /// definition with the same signature, which is what the whole table used
    /// to do for every insert.
    /// Most distinct invented-predicate constants worth enumerating flip
    /// subsets for: past this, `2^n` probes lose to one signature scan.
    const MAX_FLIPPABLE: usize = 8;

    pub(super) fn insert(&mut self, pred_def: PredDef, heap: &mut QueryHeap) {
        let Some(profile) = pred_def.key_profile(heap) else {
            // Unkeyable (a dependency inserted out of order): scan everything
            // with the same signature, as the whole table once was.
            if self.unify_against(None, &pred_def, heap) {
                return;
            }
            self.add_def(pred_def, None, heap);
            return;
        };

        let primary = key_from_profile(&profile, &[]);
        if self.unify_against(Some(primary), &pred_def, heap) {
            return;
        }

        // The profile keys an already ground reference to an invented
        // predicate by address, but the entry this definition should merge
        // with may have coined that very constant and so keyed the position
        // `OWN` (a recursive definition). Probe the alternate keys with each
        // subset of the referenced invented constants flipped to `OWN`;
        // `unify` confirms as always, so a wrong flip costs one empty lookup
        // and can never merge wrongly.
        let mut flippable: SmallVec<[usize; Self::MAX_FLIPPABLE]> = SmallVec::new();
        for (_, positions) in &profile {
            for &pos in positions {
                if pos == OWN || flippable.contains(&pos) {
                    continue;
                }
                if let (Con, symbol) = heap[pos] {
                    if self.symbol_defs.contains_key(&symbol) {
                        flippable.push(pos);
                    }
                }
            }
        }

        if flippable.len() <= Self::MAX_FLIPPABLE {
            for mask in 1u32..(1 << flippable.len()) {
                let flips: SmallVec<[usize; Self::MAX_FLIPPABLE]> = flippable
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, &addr)| addr)
                    .collect();
                let key = key_from_profile(&profile, &flips);
                if key != primary && self.unify_against(Some(key), &pred_def, heap) {
                    return;
                }
            }
        } else if self.unify_against(None, &pred_def, heap) {
            // Too many subsets to enumerate: the signature scan covers every
            // bucket an alternate key could have named.
            return;
        }

        self.add_def(pred_def, Some(primary), heap);
    }

    /// Try to unify `pred_def` onto an existing entry: the ones in `key`'s
    /// bucket, or with `None` every entry sharing its signature.
    fn unify_against(&self, key: Option<u64>, pred_def: &PredDef, heap: &mut QueryHeap) -> bool {
        let candidates: &[usize] = match key {
            Some(key) => self.buckets.get(&key).map(|b| b.as_slice()).unwrap_or(&[]),
            None => self
                .signature_index
                .get(&pred_def.signature_key())
                .map(|c| c.as_slice())
                .unwrap_or(&[]),
        };

        candidates
            .iter()
            // Pred defs from the same hypothesis are updated with bindings
            // by a successful unification.
            .any(|&i| self.get(i).unify(pred_def, heap))
    }

    /// Number of definitions.
    pub(super) fn len(&self) -> usize {
        self.pred_defs.len()
    }

    pub(super) fn get(&self, index: usize) -> PredDefRef<'_> {
        self.pred_defs.get(index)
    }

    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = PredDefRef<'_>> {
        self.pred_defs.iter()
    }

    /// The constants naming the predicates this table defines.
    pub(super) fn pred_symbols(&self) -> HashSet<usize> {
        self.symbol_defs.keys().copied().collect()
    }

    /// Append to `defs` the index of every definition `meta_subs` call,
    /// directly or through another definition; each once. `heap` holds the
    /// terms the substitutions address.
    pub(super) fn dependencies<'m>(
        &self,
        meta_subs: impl Iterator<Item = &'m [usize]>,
        heap: &impl Heap,
        defs: &mut SmallVec<[u32; 8]>,
    ) {
        let mut next = defs.len();
        for meta_sub in meta_subs {
            self.called_defs(meta_sub, heap, defs);
        }
        // `defs` doubles as the work list: each one found is scanned in turn.
        while next < defs.len() {
            let def = self.get(defs[next] as usize);
            for meta_sub in def.iter() {
                self.called_defs(meta_sub, heap, defs);
            }
            next += 1;
        }
    }

    /// Append the definitions of the invented predicates one clause names.
    fn called_defs(&self, meta_sub: &[usize], heap: &impl Heap, defs: &mut SmallVec<[u32; 8]>) {
        for sub in meta_sub.subs() {
            let Some(Addr(addr)) = sub.get_bind() else {
                continue;
            };
            let (Con, symbol) = heap[addr] else {
                continue;
            };
            if let Some(def) = self.symbol_defs.get(&symbol) {
                if !defs.contains(def) {
                    defs.push(*def);
                }
            }
        }
    }

    /// Everything needed to prove with `hypothesis`: its own clauses, then
    /// those of every definition it depends on.
    pub(super) fn test_meta_subs<'a>(
        &'a self,
        hypothesis: MetaSubGroup<'a>,
        heap: &impl Heap,
    ) -> SmallVec<[&'a [usize]; 8]> {
        let mut defs = SmallVec::new();
        self.dependencies(hypothesis.iter(), heap, &mut defs);

        let mut meta_subs: SmallVec<[&'a [usize]; 8]> = hypothesis.iter().collect();
        for def in defs {
            let def = self.get(def as usize);
            meta_subs.extend((0..def.len()).map(|clause| def.get(clause)));
        }
        meta_subs
    }

    fn add_def(&mut self, mut pred_def: PredDef, key: Option<u64>, heap: &mut QueryHeap) {
        pred_def.make_const(heap);

        // Read the head constants back rather than having `make_const` report
        // them: a definition whose head was already coined -- by an earlier
        // clause of the same mutually recursive group, or by unification
        // against the table -- mints nothing, and its constant still names an
        // invented predicate.
        let index = u32::try_from(self.pred_defs.len()).expect("more than u32::MAX definitions");
        for meta_sub in &pred_def.meta_subs {
            if let Some(Addr(addr)) = meta_sub.subs.first().and_then(|sub| sub.get_bind()) {
                if let (Con, symbol) = heap[addr] {
                    self.symbol_defs.insert(symbol, index);
                }
            }
        }

        // The primary key computed before grounding is still correct after
        // it: `make_const` only rewrites positions from variable bindings to
        // the addresses they already dereferenced to, and the positions it
        // coins constants for are exactly the ones the profile already
        // classified `Own`. A definition that could not be keyed before
        // grounding can be now, and must be, so that later references to its
        // coined constants find it by key.
        let key = key.unwrap_or_else(|| {
            let profile = pred_def
                .key_profile(heap)
                .expect("a grounded definition has no unbound positions left to block its key");
            key_from_profile(&profile, &[])
        });

        let index = self.pred_defs.len();
        self.buckets.entry(key).or_default().push(index);
        self.signature_index
            .entry(pred_def.signature_key())
            .or_default()
            .push(index);
        self.pred_defs.push(&pred_def.meta_subs);
    }

    /// Debug aid: print each definition as its meta clause ids and the terms
    /// substituted into them.
    ///
    /// A `PredDef` holds substitutions rather than clauses, and rebuilding the
    /// clauses would need a mutable heap and the predicate table holding the
    /// templates -- more than a print wants -- so this shows the substitution
    /// itself.
    pub(super) fn _print_defs(&self, heap: &impl Heap) {
        for (i, pred_def) in self.iter().enumerate() {
            println!("====== Definition {i} ======");
            for msub in pred_def.iter() {
                let subs: Vec<String> = msub
                    .subs()
                    .map(|sub| match sub.get_bind() {
                        Some(Addr(addr)) => heap.term_string(addr),
                        Some(VarId(var_id)) => format!("Var_{var_id}"),
                        None => "UNBOUND".to_string(),
                    })
                    .collect();
                println!("meta clause {}: {}", msub.clause_idx(), subs.join(", "));
            }
            println!("===========================");
        }
    }

    /// Extract and insert a test hypothesis's definitions.
    #[cfg(test)]
    pub(super) fn extract_pred_defs_from_h(
        &mut self,
        meta_subs: &mut Vec<MetaSub>,
        predicate_table: &PredicateTable,
        heap: &mut QueryHeap,
    ) {
        for pred_def in PredDef::extract_from_test_hypothesis(meta_subs, predicate_table, heap) {
            self.insert(pred_def, heap);
        }
    }
}

#[cfg(test)]
impl PredDef {
    /// [`Self::extract_pred_defs_from_h`] for a hypothesis the tests built.
    ///
    /// They build their hypotheses before their predicate table, so each
    /// `MetaSub` arrives holding its meta rule's *id*; that is swapped for
    /// the arena index first.
    pub(super) fn extract_from_test_hypothesis(
        meta_subs: &mut Vec<MetaSub>,
        predicate_table: &PredicateTable,
        heap: &impl Heap,
    ) -> Vec<Self> {
        for meta_sub in meta_subs.iter_mut() {
            let meta_clause = predicate_table
                .get_meta_clause(meta_sub.clause_idx)
                .expect("the test's meta rule is in its table");
            meta_sub.clause_idx = predicate_table.index_of(meta_clause).unwrap();
        }
        Self::extract_pred_defs_from_h(meta_subs, predicate_table, heap)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        heap::{
            ArgRegs, Heap, ProgramHeap, QueryHeap,
            Tag::*,
            VarBind::{self, *},
            VarReg,
        },
        learners::predicate_unification::{PredDef, PredDefLike, PredDefTable},
        parser::_build_clause,
        program::{Clause, Constraints, Hypothesis, MetaSubTrait, PackedMetaSubs, PredicateTable},
        resolution::{build, Proof, Substitution},
        Config,
    };
    use smallvec::SmallVec;

    /// Intern `symbols` in `prog`'s table.
    ///
    /// Takes the heap because each test builds its own: ids from any other
    /// table would not name these symbols in the heap under test.
    fn get_const_ids<const N: usize>(prog: &ProgramHeap, symbols: [&'static str; N]) -> [usize; N] {
        let mut res = [0; N];

        for i in 0..N {
            res[i] = prog.symbols().set_const(symbols[i])
        }

        res
    }

    /// A predicate table holding `rules`, for looking meta clauses up by id.
    fn table_of(prog: &ProgramHeap, rules: &[&Clause]) -> PredicateTable {
        let mut table = PredicateTable::new();
        for rule in rules {
            let symbol_arity = prog.symbol_arity(rule.head());
            table
                .add_clause_to_predicate((*rule).clone(), symbol_arity)
                .unwrap();
        }
        table
    }

    fn instantiate_meta_rule(
        heap: &mut QueryHeap,
        meta: &Clause,
        bindings: &[(usize, VarBind)],
    ) -> (Clause, ArgRegs) {
        let mut subs = Substitution::new(15);
        for (arg_id, binding) in bindings {
            subs.set_arg(*arg_id, *binding);
        }

        let new_clause_literals: Vec<usize> = meta
            .iter()
            .map(|literal| build(heap, &mut subs, meta.meta_threshold(), *literal))
            .collect();

        (
            Clause::new(new_clause_literals, None, meta.max_arg_id),
            subs.arg_regs,
        )
    }

    fn build_hypothesis<const N: usize, const M: usize>(
        meta_rules: [(&Clause, usize); N],
        meta_binds: [(usize, &[VarBind]); M],
        heap: &mut QueryHeap,
    ) -> Hypothesis {
        let mut h = Hypothesis::new();
        // Ensure heap has var regs
        let mut max_var_id = 0;
        for (_, binds) in &meta_binds {
            for bind in *binds {
                if let VarId(var_id) = bind {
                    max_var_id = max_var_id.max(*var_id);
                }
            }
        }
        if heap.var_regs.len() <= max_var_id {
            heap.var_regs.resize(max_var_id + 1, VarReg::UNBOUND);
        }

        for (meta_idx, bindings) in meta_binds {
            let (meta_rule, reg_offset) = meta_rules[meta_idx];
            let bindings: Box<[(usize, VarBind)]> = bindings
                .into_iter()
                .enumerate()
                .map(|(i, bind)| (i + reg_offset, bind.clone()))
                .collect();
            let (_, arg_regs) = instantiate_meta_rule(heap, meta_rule, &bindings);
            // The rule's id for now: the table is built after the
            // hypotheses, so the test-only
            // `PredDefTable::extract_pred_defs_from_h` swaps it for the
            // arena index.
            h.push_clause(
                meta_rule,
                meta_rule.meta_data.unwrap().id,
                Constraints::default(),
                &arg_regs,
            );
        }

        h
    }

    /// No two entries in the table may unify with each other.
    ///
    /// Every entry has been through `make_const`, so all of its substitutions
    /// are addresses and `unify` degenerates to a structural comparison that
    /// binds nothing -- making this safe to run pairwise over a finished
    /// table. A pair that does unify is a definition that should have been
    /// merged into an existing entry when it was inserted, and each one that
    /// escapes mints another `pred_N` and fragments every hypothesis
    /// mentioning it.
    fn assert_table_has_no_duplicates(pdt: &PredDefTable, heap: &mut QueryHeap) {
        for i in 0..pdt.len() {
            for j in (i + 1)..pdt.len() {
                assert!(
                    !pdt.get(i).unify(&pdt.get(j), heap),
                    "table entries {i} and {j} unify, so one of them is a duplicate"
                );
            }
        }
    }

    /// Two hypotheses inventing the same predicate under different variables
    /// must collapse to a single table entry.
    #[test]
    fn identical_definitions_collapse_to_one_entry() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (1, &[VarId(0), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);

        assert_eq!(pdt.len(), 1, "both hypotheses invent the same predicate");
        assert_eq!(heap.var_deref(0), heap.var_deref(1));
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// Definitions that genuinely differ must stay separate, and each must
    /// get its own coined constant.
    #[test]
    fn differing_definitions_stay_separate() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r, s] = get_const_ids(&prog_heap, ["p", "q", "r", "s"]);
        let [p, q, r, s] = [p, q, r, s].map(|con_id| heap.heap_push((Con, con_id)));

        // Var_0 is q-then-r, Var_1 is q-then-s: different definitions.
        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (1, &[VarId(0), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(s)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);

        assert_eq!(pdt.len(), 2);
        assert_ne!(heap.var_deref(0), heap.var_deref(1));
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// A two-clause definition must merge regardless of the order its clauses
    /// happen to be found in -- `PredDef::unify` searches for a pairing
    /// rather than comparing position by position.
    #[test]
    fn clause_order_within_a_definition_does_not_matter() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (1, &[VarId(0), Addr(q), Addr(r)]),
                (1, &[VarId(0), Addr(r), Addr(q)]),
            ],
            &mut heap,
        );
        // Same two clauses, discovered the other way round.
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(1)]),
                (1, &[VarId(1), Addr(r), Addr(q)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);

        assert_eq!(
            pdt.len(),
            1,
            "the same two clauses in the other order are the same definition"
        );
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// The head predicate variable each definition defines, in the order the
    /// definitions were returned.
    fn definition_heads(defs: &[PredDef]) -> Vec<usize> {
        defs.iter()
            .map(|def| match def.meta_subs[0].subs[0].get_bind() {
                Some(VarId(var_id)) => var_id,
                other => panic!("expected an unbound head predicate variable, got {other:?}"),
            })
            .collect()
    }

    /// A definition whose body names another invented predicate must be
    /// inserted into the table *after* that predicate's own definition.
    ///
    /// Until the dependency is inserted its head variable is unbound, and an
    /// unbound variable unifies with anything -- so a dependent inserted first
    /// can match the wrong definition in the table and bind the shared
    /// variable to the wrong coined constant.
    ///
    /// Hypothesis
    ///     p(X,Y):- Var_0(X,Y).      (constant head, not a definition)
    ///     Var_0(X,Y):- Var_1(X,Y).  (depends on Var_1)
    ///     Var_1(X,Y):- q(X), r(Y).
    #[test]
    fn dependencies_are_defined_before_their_dependents() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let defs = PredDef::extract_from_test_hypothesis(&mut h.meta_subs, &table, &heap);

        assert_eq!(
            definition_heads(&defs),
            vec![1, 0],
            "Var_1 is named in Var_0's body, so Var_1 must be defined first"
        );
    }

    /// The same requirement when the dependency is recursive.
    ///
    /// Self-recursion puts a cycle in the dependency graph, which sends
    /// `extract_pred_defs_from_h` down `ordered_cyclic_groups` instead of
    /// `order`. The two used to sort in opposite directions, so adding a
    /// single recursive clause silently reversed the insertion order.
    ///
    /// Hypothesis
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- Var_1(X,Y).
    #[test]
    fn a_recursive_dependency_is_still_defined_first() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta_rules = [(&meta0, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p] = get_const_ids(&prog_heap, ["p"]);
        let [p] = [p].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(1), VarId(1)]),
            ],
            &mut heap,
        );

        let defs = PredDef::extract_from_test_hypothesis(&mut h.meta_subs, &table, &heap);

        assert_eq!(
            definition_heads(&defs),
            vec![1, 0],
            "the recursive predicate must be defined before the one using it"
        );
    }

    /// A hypothesis inventing more than eight predicates, which no longer
    /// falls to `todo!` but switches to the 16-node dependency graph.
    ///
    /// A chain of nine definitions, each calling the next:
    ///     p(X,Y):- Var_0(X,Y).      (constant head, not a definition)
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     ...
    ///     Var_7(X,Y):- Var_8(X,Y).
    ///     Var_8(X,Y):- q(X), r(Y).
    /// so the order must be the chain reversed, deepest dependency first.
    #[test]
    fn more_than_eight_invented_predicates_are_ordered() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)] as &[VarBind]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(1), VarId(2)]),
                (0, &[VarId(2), VarId(3)]),
                (0, &[VarId(3), VarId(4)]),
                (0, &[VarId(4), VarId(5)]),
                (0, &[VarId(5), VarId(6)]),
                (0, &[VarId(6), VarId(7)]),
                (0, &[VarId(7), VarId(8)]),
                (1, &[VarId(8), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let defs = PredDef::extract_from_test_hypothesis(&mut h.meta_subs, &table, &heap);

        assert_eq!(defs.len(), 9, "nine invented predicates, nine definitions");
        assert_eq!(
            definition_heads(&defs),
            vec![8, 7, 6, 5, 4, 3, 2, 1, 0],
            "each definition must come after the one it calls"
        );
    }

    /// The same, inserted, to confirm the wider graph still grounds every
    /// shared variable in the right order.
    #[test]
    fn more_than_eight_invented_predicates_all_ground() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)] as &[VarBind]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(1), VarId(2)]),
                (0, &[VarId(2), VarId(3)]),
                (0, &[VarId(3), VarId(4)]),
                (0, &[VarId(4), VarId(5)]),
                (0, &[VarId(5), VarId(6)]),
                (0, &[VarId(6), VarId(7)]),
                (0, &[VarId(7), VarId(8)]),
                (1, &[VarId(8), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h.meta_subs, &table, &mut heap);

        assert_eq!(pdt.len(), 9);
        assert_eq!(pdt.pred_symbols().len(), 9, "one constant per definition");
        for var_id in 0..9 {
            assert!(
                matches!(heap.var_deref(var_id), Addr(_)),
                "Var_{var_id} should be bound to a coined constant"
            );
        }
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// Inserting in that order is what grounds the shared variable: by the
    /// time the dependent is inserted, the body predicate it names already
    /// derefs to the constant coined for the dependency's head.
    #[test]
    fn inserting_in_order_grounds_the_shared_variable() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h.meta_subs, &table, &mut heap);

        // Both variables are now ground, and to *different* predicates: Var_0
        // is the caller, Var_1 the callee.
        let (Addr(var0), Addr(var1)) = (heap.var_deref(0), heap.var_deref(1)) else {
            panic!("every invented predicate should be bound to a coined constant");
        };
        assert_ne!(heap[var0], heap[var1]);

        // The body position of Var_0's definition names exactly the constant
        // coined for Var_1's head.
        let var_0_def = pdt
            .iter()
            .find(|def| matches!(def.get(0).subs().nth(0).unwrap().get_bind(), Some(Addr(a)) if heap[a] == heap[var0]))
            .expect("Var_0 should have a definition in the table");
        let Some(Addr(body)) = var_0_def.get(0).subs().nth(1).unwrap().get_bind() else {
            panic!("the body predicate should be ground");
        };
        assert_eq!(heap[body], heap[var1]);
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    #[test]
    fn one_clause_pred() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (1, &[VarId(0), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();

        //Seperate out pred defs
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);

        pdt._print_defs(&heap);

        assert_eq!(heap.var_deref(0), heap.var_deref(1))
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- q(X), r(Y).
    ///     Var_0(X,Y):- r(X), q(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    ///     Var_1(X,Y):- r(X), q(Y).
    #[test]
    fn two_clause_pred() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (1, &[VarId(0), Addr(q), Addr(r)]),
                (1, &[VarId(0), Addr(r), Addr(q)]),
            ],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
                (1, &[VarId(1), Addr(r), Addr(q)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();

        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);

        pdt._print_defs(&heap);

        assert_eq!(heap.var_deref(0), heap.var_deref(1));
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y)
    ///     Var_1(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_2(X,Y).
    ///     Var_2(X,Y):- Var_3(X,Y).
    ///     Var_3(X,Y):- q(X), r(Y).
    #[test]
    fn dependent_pred() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(2)]),
                (0, &[VarId(2), VarId(3)]),
                (1, &[VarId(3), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);
        pdt._print_defs(&heap);

        assert_eq!(heap.var_deref(0), heap.var_deref(2));
        assert_eq!(heap.var_deref(1), heap.var_deref(3));
    }

    /// Bind each remaining predicate variable to the constant coined for it,
    /// as merging does, and pack the hypothesis.
    fn pack_grounded(h: &mut Hypothesis, heap: &QueryHeap, packed: &mut PackedMetaSubs) {
        for meta_sub in &mut h.meta_subs {
            for sub in &mut meta_sub.subs {
                if let Some(VarId(var_id)) = sub.get_bind() {
                    let bound = heap.var_deref(var_id);
                    assert!(
                        matches!(bound, Addr(_)),
                        "every invented predicate is defined"
                    );
                    *sub = bound.into();
                }
            }
        }
        packed.push(h.meta_subs.iter());
    }

    /// Hypothesis 1, which reaches its second definition only through its
    /// first:
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    /// Hypothesis 2:
    ///     p(X,Y):- Var_2(X,Y).
    ///     Var_2(X,Y):- r(X), q(Y).
    #[test]
    fn a_hypothesis_is_proved_from_its_meta_subs_and_its_definitions() {
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let q_fact = _build_clause(&mut prog_heap, "q(a).");
        let r_fact = _build_clause(&mut prog_heap, "r(b).");
        let p_a_b = _build_clause(&mut prog_heap, "p(a,b).")[0];
        let p_b_a = _build_clause(&mut prog_heap, "p(b,a).")[0];
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &[&meta0, &meta1, &q_fact, &r_fact]);

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(2)]),
                (1, &[VarId(2), Addr(r), Addr(q)]),
            ],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);
        assert_eq!(pdt.len(), 3);

        let mut hypotheses = PackedMetaSubs::default();
        pack_grounded(&mut h1, &heap, &mut hypotheses);
        pack_grounded(&mut h2, &heap, &mut hypotheses);

        let mut defs = SmallVec::new();
        pdt.dependencies(hypotheses.get(0).iter(), &heap, &mut defs);
        assert_eq!(
            defs.len(),
            2,
            "the second definition is reached through the first"
        );
        // Asking again finds nothing new.
        pdt.dependencies(hypotheses.get(0).iter(), &heap, &mut defs);
        assert_eq!(defs.len(), 2);

        let config = Config {
            max_depth: 10,
            max_clause: 0,
            debug: false,
            protect_h_preds: true,
        };
        // Which of `p(a,b)` and `p(b,a)` each hypothesis proves, given
        // `q(a)` and `r(b)`.
        for (index, clauses, proves) in [(0, 3, [true, false]), (1, 2, [false, true])] {
            let meta_subs = pdt.test_meta_subs(hypotheses.get(index), &heap);
            assert_eq!(meta_subs.len(), clauses);
            for (goal, expected) in [p_a_b, p_b_a].into_iter().zip(proves) {
                let mut proof = Proof::with_hypothesis(&heap, &[goal], meta_subs.as_slice());
                assert_eq!(proof.prove(&mut heap, &table, config), expected);
                proof.undo_all(&mut heap);
            }
        }
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     Var_0(X,Y):- p(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_2(X,Y).
    ///     Var_2(X,Y):- Var_3(X,Y).
    ///     Var_3(X,Y):- q(X), r(Y).
    #[test]
    fn dependend_different() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));
        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(0), Addr(p)]),
                (1, &[VarId(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(2)]),
                (0, &[VarId(2), VarId(3)]),
                (1, &[VarId(3), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        // Build Pred Def table
        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);
        pdt._print_defs(&heap);

        assert_ne!(heap.var_deref(0), heap.var_deref(2));
        assert_eq!(heap.var_deref(1), heap.var_deref(3));
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- Var_0(X,Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_2(X,Y).
    ///     Var_2(X,Y):- Var_3(X,Y).
    ///     Var_3(X,Y):- Var_2(X,Y).
    #[test]
    fn simple_mutual() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta_rules = [(&meta0, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, _, _] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));
        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(1), VarId(0)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(2)]),
                (0, &[VarId(2), VarId(3)]),
                (0, &[VarId(3), VarId(2)]),
            ],
            &mut heap,
        );

        // Build Pred Def table
        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);
        pdt._print_defs(&heap);

        let (Addr(addr1), Addr(addr2)) = (heap.var_deref(0), heap.var_deref(2)) else {
            panic!()
        };
        assert_eq!(heap[addr1], heap[addr2]);

        let (Addr(addr1), Addr(addr2)) = (heap.var_deref(1), heap.var_deref(3)) else {
            panic!()
        };
        assert_eq!(heap[addr1], heap[addr2]);
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- Var_1(X,Y).
    ///     Var_0(X,Y):- Var_2(X,Y).
    ///     Var_1(X,Y):- Var_0(X,Y).
    ///     Var_2(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_3(X,Y):- Var_4(X,Y).
    ///     Var_3(X,Y):- Var_5(X,Y).
    ///     Var_4(X,Y):- Var_3(X,Y).
    ///     Var_5(X,Y):- q(X), r(Y).
    #[test]
    fn mutual_dependent() {
        // Create meta rules
        let mut prog_heap = ProgramHeap::new();
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];
        let table = table_of(&prog_heap, &meta_rules.map(|(rule, _)| rule));

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(&prog_heap, ["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));
        let mut h1 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(0), VarId(1)]),
                (0, &[VarId(0), VarId(2)]),
                (0, &[VarId(1), VarId(0)]),
                (1, &[VarId(2), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), VarId(0)]),
                (0, &[VarId(3), VarId(4)]),
                (0, &[VarId(3), VarId(5)]),
                (0, &[VarId(4), VarId(3)]),
                (1, &[VarId(5), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        // Build Pred Def table
        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.meta_subs, &table, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.meta_subs, &table, &mut heap);
        pdt._print_defs(&heap);

        let (Addr(addr1), Addr(addr2)) = (heap.var_deref(0), heap.var_deref(3)) else {
            panic!()
        };
        assert_eq!(heap[addr1], heap[addr2]);

        let (Addr(addr1), Addr(addr2)) = (heap.var_deref(1), heap.var_deref(4)) else {
            panic!()
        };
        assert_eq!(heap[addr1], heap[addr2]);

        let (Addr(addr1), Addr(addr2)) = (heap.var_deref(2), heap.var_deref(5)) else {
            panic!()
        };
        assert_eq!(heap[addr1], heap[addr2]);
    }
}
