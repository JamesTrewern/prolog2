use std::{
    cmp::Ordering::{self, *},
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut, Range},
};

use smallvec::SmallVec;

use crate::{
    heap::{
        Heap, QueryHeap, SymbolDB,
        Tag::*,
        VarBind::{Addr, VarId},
    },
    program::{clause::Clause, meta_sub::MetaSub},
    utils::{DirGraph16, DirGraph8, FindReturn},
};

/// Most invented predicates one sub hypothesis can define.
///
/// Set by the widest dependency graph available
/// ([`DirGraph16`](crate::utils::DirGraph16)). A hypothesis cannot invent
/// more predicates than it has clauses, so bounding `max_clause` by this
/// bounds the number of clause sets too.
pub const MAX_PRED_DEFS: usize = 16;

#[derive(Debug)]
pub struct PredDef {
    pub meta_subs: SmallVec<[MetaSub; 4]>,
    meta_clause_ranges: HashMap<usize, (usize, usize)>,
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
    pub fn new(mut meta_subs: SmallVec<[MetaSub; 4]>) -> Self {
        meta_subs.sort_by_key(|meta_sub| meta_sub.meta_clause_id);
        let mut meta_clause_ranges = HashMap::new();
        let mut start = 0;
        for i in 1..meta_subs.len() {
            if meta_subs[i - 1].meta_clause_id != meta_subs[i].meta_clause_id {
                meta_clause_ranges.insert(meta_subs[i - 1].meta_clause_id, (start, i));
                start = i;
            }
        }
        meta_clause_ranges.insert(
            meta_subs.last().unwrap().meta_clause_id,
            (start, meta_subs.len()),
        );

        Self {
            meta_subs,
            meta_clause_ranges,
        }
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
    pub fn make_const(&mut self, heap: &mut impl Heap, next_id: &mut usize) {
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
                        let pred_symbol = SymbolDB::set_const(format!("pred_{next_id}"));
                        let addr = heap.heap_push((Con, pred_symbol));
                        *next_id += 1;
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

    /// Attempt to unify two clause definitions
    /// Self should be constant
    /// will update variable bindings on heap effecting other variable clause defintions waiting to unify
    pub fn unify(&self, other: &PredDef, heap: &mut QueryHeap) -> bool {
        // TODO consider if different meta_rules might result in the same clause
        if self.cmp(other) != Equal {
            return false;
        }
        let mut stack: Vec<(usize, Vec<usize>)> = Vec::new(); // (last matched index, bindings)
        let mut unified = vec![false; self.len()].into_boxed_slice();
        let mut i = 0;
        'outer: while i < other.len() {
            let (s, e) = *self
                .meta_clause_ranges
                .get(&other[i].meta_clause_id)
                .unwrap();

            // Fresh visit to this position: start the search at the range's
            // first index. A revisit (backtrack) undoes the previous match
            // at this position and resumes the search just after it.
            let start = if i == stack.len() {
                stack.push((s, Vec::new()));
                s
            } else {
                let (last_j, bindings) = &stack[i];
                unified[*last_j] = false;
                heap.unbind(bindings);
                last_j + 1
            };

            //Attempt to find clause to unify with
            for j in start..e {
                if unified[j] {
                    continue;
                }
                if let Some(binding) = self[j].unify(&other[i], heap) {
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

    pub fn cmp(&self, other: &Self) -> Ordering {
        match self.meta_subs.len().cmp(&other.meta_subs.len()) {
            Equal => {
                for (msub1, msub2) in self.meta_subs.iter().zip(other.meta_subs.iter()) {
                    match msub1.meta_clause_id.cmp(&msub2.meta_clause_id) {
                        Equal => continue,
                        ordering => return ordering,
                    }
                }
                Equal
            }
            ord => ord,
        }
    }

    pub fn extract_pred_defs_from_h(
        clauses: &mut Vec<Clause>,
        meta_subs: &mut Vec<MetaSub>,
        heap: &impl Heap,
    ) -> Vec<Self> {
        let mut clause_sets: Vec<SmallVec<[(Clause, MetaSub); 4]>> =
            Vec::with_capacity(clauses.len());
        let mut var_preds = Vec::with_capacity(clauses.len());
        let mut dependencies: Vec<HashSet<usize>> = Vec::with_capacity(clauses.len());

        for idx in (0..clauses.len()).rev() {
            if let (Var, var_id) = heap.get_deref_cell(clauses[idx].head() + 1) {
                let clause = clauses.remove(idx);
                let meta_sub = meta_subs.remove(idx);
                match var_preds.iter().position(|var_pred| *var_pred == var_id) {
                    Some(def_index) => {
                        extract_body_var_preds(&mut dependencies[def_index], &clause, heap);
                        clause_sets[def_index].push((clause, meta_sub));
                    }
                    None => {
                        var_preds.push(var_id);
                        let mut body_var_preds = HashSet::new();
                        extract_body_var_preds(&mut body_var_preds, &clause, heap);
                        dependencies.push(body_var_preds);
                        clause_sets.push(SmallVec::from_elem((clause, meta_sub), 1));
                    }
                }
            }
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
                let mut meta_subs: SmallVec<[MetaSub; 4]> = SmallVec::new();
                for (i, clause_set) in clause_sets.iter_mut().enumerate() {
                    if group & 1 << i != 0 {
                        meta_subs.extend(clause_set.drain(..).map(|(_, msub)| msub));
                    }
                }
                PredDef::new(meta_subs)
            })
            .collect()
    }
}

#[derive(Default, Debug)]
pub struct PredDefTable {
    pub pred_defs: Vec<PredDef>,
    pub next_id: usize,
    /// Symbol ids of the constants coined to name the predicates defined
    /// here, recorded as each definition is inserted.
    ///
    /// These are what distinguishes an invented predicate from a background
    /// one. Recognising them by symbol id -- rather than by comparing against
    /// the id of `pred_0`, which assumes every background predicate was
    /// interned before the first invented one -- keeps the answer correct
    /// whatever order the symbol table happened to be filled in.
    pred_symbols: HashSet<usize>,
}

impl PredDefTable {
    pub fn insert(&mut self, pred_def: PredDef, heap: &mut QueryHeap) {
        match self.binary_search(&pred_def) {
            FindReturn::InsertPos(insert_pos) => self.add_def(pred_def, insert_pos, heap),
            FindReturn::Index(i) => {
                let matching_range = self.find_matching_signature_range(&pred_def, i);
                let insert_pos = matching_range.start;
                // Attempt to unify with existing pred def
                for i in matching_range {
                    if self.pred_defs[i].unify(&pred_def, heap) {
                        // Unification successful
                        // Pred defs from same hypothesis now updated with bindings
                        return;
                    }
                }
                //Insert new pred def at start of range
                self.add_def(pred_def, insert_pos, heap);
            }
        }
    }

    /// The constants naming the predicates this table defines.
    pub fn pred_symbols(&self) -> &HashSet<usize> {
        &self.pred_symbols
    }

    fn add_def(&mut self, mut pred_def: PredDef, insert_pos: usize, heap: &mut QueryHeap) {
        pred_def.make_const(heap, &mut self.next_id);
        self.next_id += 1;

        // Read the head constants back rather than having `make_const` report
        // them: a definition whose head was already coined -- by an earlier
        // clause of the same mutually recursive group, or by unification
        // against the table -- mints nothing, and its constant still names an
        // invented predicate.
        for meta_sub in &pred_def.meta_subs {
            if let Some(Addr(addr)) = meta_sub.subs.first().and_then(|sub| sub.get_bind()) {
                if let (Con, symbol) = heap[addr] {
                    self.pred_symbols.insert(symbol);
                }
            }
        }

        self.pred_defs.insert(insert_pos, pred_def);
    }

    fn binary_search(&self, pred_def: &PredDef) -> FindReturn {
        let mut lb: usize = 0;
        let mut ub: usize = self.pred_defs.len();
        let mut mid: usize;

        while ub > lb {
            mid = (lb + ub) / 2;
            match pred_def.cmp(&self.pred_defs[mid]) {
                Less => ub = mid,
                Equal => return FindReturn::Index(mid),
                Greater => lb = mid + 1,
            }
        }
        FindReturn::InsertPos(lb)
    }

    fn find_matching_signature_range(&self, pred_def: &PredDef, i: usize) -> Range<usize> {
        let mut lb = i;

        while lb > 0 && self.pred_defs[lb - 1].cmp(&pred_def) == Equal {
            lb -= 1;
        }
        let mut ub = i + 1;
        while ub < self.pred_defs.len() && self.pred_defs[ub].cmp(&pred_def) == Equal {
            ub += 1;
        }
        lb..ub
    }

    /// Debug aid: print each definition as its meta clause ids and the terms
    /// substituted into them.
    ///
    /// A `PredDef` holds substitutions rather than clauses, and rebuilding the
    /// clauses would need a mutable heap and the predicate table holding the
    /// templates -- more than a print wants -- so this shows the substitution
    /// itself.
    pub fn _print_defs(&self, heap: &impl Heap) {
        for (i, pred_def) in self.pred_defs.iter().enumerate() {
            println!("====== Definition {i} ======");
            for msub in &pred_def.meta_subs {
                let subs: Vec<String> = msub
                    .subs
                    .iter()
                    .map(|sub| match sub.get_bind() {
                        Some(Addr(addr)) => heap.term_string(addr),
                        Some(VarId(var_id)) => format!("Var_{var_id}"),
                        None => "UNBOUND".to_string(),
                    })
                    .collect();
                println!("meta clause {}: {}", msub.meta_clause_id, subs.join(", "));
            }
            println!("===========================");
        }
    }

    #[cfg(test)]
    pub fn extract_pred_defs_from_h(
        &mut self,
        clauses: &mut Vec<Clause>,
        meta_subs: &mut Vec<MetaSub>,
        heap: &mut QueryHeap,
    ) {
        for pred_def in PredDef::extract_pred_defs_from_h(clauses, meta_subs, heap) {
            self.insert(pred_def, heap);
        }
    }
}

fn extract_body_var_preds(pred_set: &mut HashSet<usize>, clause: &Clause, heap: &impl Heap) {
    for literal in clause.body() {
        if let (Var, var_id) = heap.get_deref_cell(literal + 1) {
            pred_set.insert(var_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        heap::{
            ArgRegs, Cell, Heap, QueryHeap, SymbolDB,
            Tag::*,
            VarBind::{self, *},
            VarReg,
        },
        learners::predicate_unification::{PredDef, PredDefTable},
        parser::_build_clause,
        program::{
            clause::Clause,
            hypothesis::{Constraints, Hypothesis},
        },
        resolution::{build, Substitution},
    };

    fn get_const_ids<const N: usize>(symbols: [&'static str; N]) -> [usize; N] {
        let mut res = [0; N];

        for i in 0..N {
            res[i] = SymbolDB::set_const(symbols[i])
        }

        res
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
            .map(|literal| build(heap, &mut subs, meta.meta_vars(), *literal))
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
            let (clause, arg_regs) = instantiate_meta_rule(heap, meta_rule, &bindings);
            h.push_clause(
                clause,
                Constraints::default(),
                &arg_regs,
                meta_rule.meta_data.unwrap(),
            );
        }

        h
    }

    fn print_hypothesis(clauses: &[Clause], id: usize, heap: &impl Heap) {
        println!("=====================");
        println!("Hypothesis {id}");
        for c in clauses {
            println!("{}", c.to_string(heap))
        }
        println!("=====================");
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
        for i in 0..pdt.pred_defs.len() {
            for j in (i + 1)..pdt.pred_defs.len() {
                assert!(
                    !pdt.pred_defs[i].unify(&pdt.pred_defs[j], heap),
                    "table entries {i} and {j} unify, so one of them is a duplicate"
                );
            }
        }
    }

    /// Two hypotheses inventing the same predicate under different variables
    /// must collapse to a single table entry.
    #[test]
    fn identical_definitions_collapse_to_one_entry() {
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(0)]), (1, &[VarId(0), Addr(q), Addr(r)])],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(1)]), (1, &[VarId(1), Addr(q), Addr(r)])],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);

        assert_eq!(
            pdt.pred_defs.len(),
            1,
            "both hypotheses invent the same predicate"
        );
        assert_eq!(heap.var_deref(0), heap.var_deref(1));
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// Definitions that genuinely differ must stay separate, and each must
    /// get its own coined constant.
    #[test]
    fn differing_definitions_stay_separate() {
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r, s] = get_const_ids(["p", "q", "r", "s"]);
        let [p, q, r, s] = [p, q, r, s].map(|con_id| heap.heap_push((Con, con_id)));

        // Var_0 is q-then-r, Var_1 is q-then-s: different definitions.
        let mut h1 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(0)]), (1, &[VarId(0), Addr(q), Addr(r)])],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(1)]), (1, &[VarId(1), Addr(q), Addr(s)])],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);

        assert_eq!(pdt.pred_defs.len(), 2);
        assert_ne!(heap.var_deref(0), heap.var_deref(1));
        assert_table_has_no_duplicates(&pdt, &mut heap);
    }

    /// A two-clause definition must merge regardless of the order its clauses
    /// happen to be found in -- `PredDef::unify` searches for a pairing
    /// rather than comparing position by position.
    #[test]
    fn clause_order_within_a_definition_does_not_matter() {
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);

        assert_eq!(
            pdt.pred_defs.len(),
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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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

        let defs = PredDef::extract_pred_defs_from_h(&mut h.clauses, &mut h.meta_subs, &heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta_rules = [(&meta0, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p] = get_const_ids(["p"]);
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

        let defs = PredDef::extract_pred_defs_from_h(&mut h.clauses, &mut h.meta_subs, &heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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

        let defs = PredDef::extract_pred_defs_from_h(&mut h.clauses, &mut h.meta_subs, &heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h.clauses, &mut h.meta_subs, &mut heap);

        assert_eq!(pdt.pred_defs.len(), 9);
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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h.clauses, &mut h.meta_subs, &mut heap);

        // Both variables are now ground, and to *different* predicates: Var_0
        // is the caller, Var_1 the callee.
        let (Addr(var0), Addr(var1)) = (heap.var_deref(0), heap.var_deref(1)) else {
            panic!("every invented predicate should be bound to a coined constant");
        };
        assert_ne!(heap[var0], heap[var1]);

        // The body position of Var_0's definition names exactly the constant
        // coined for Var_1's head.
        let var_0_def = pdt
            .pred_defs
            .iter()
            .find(|def| matches!(def.meta_subs[0].subs[0].get_bind(), Some(Addr(a)) if heap[a] == heap[var0]))
            .expect("Var_0 should have a definition in the table");
        let Some(Addr(body)) = var_0_def.meta_subs[0].subs[1].get_bind() else {
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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(0)]), (1, &[VarId(0), Addr(q), Addr(r)])],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), VarId(1)]), (1, &[VarId(1), Addr(q), Addr(r)])],
            &mut heap,
        );

        let mut pdt = PredDefTable::default();

        //Seperate out pred defs
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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

        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);
        pdt._print_defs(&heap);

        assert_eq!(heap.var_deref(0), heap.var_deref(2));
        assert_eq!(heap.var_deref(1), heap.var_deref(3));
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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);
        pdt._print_defs(&heap);

        print_hypothesis(&h1, 1, &heap);
        print_hypothesis(&h2, 2, &heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta_rules = [(&meta0, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);
        pdt._print_defs(&heap);

        print_hypothesis(&h1, 1, &heap);
        print_hypothesis(&h2, 2, &heap);

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
        let mut prog_heap: Vec<Cell> = vec![];
        let meta0 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let meta_rules = [(&meta0, 2), (&meta1, 2)];

        //Build hypotheses
        let mut heap = QueryHeap::new(&prog_heap, None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
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
        pdt.extract_pred_defs_from_h(&mut h1.clauses, &mut h1.meta_subs, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2.clauses, &mut h2.meta_subs, &mut heap);
        pdt._print_defs(&heap);

        print_hypothesis(&h1, 1, &heap);
        print_hypothesis(&h2, 2, &heap);

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
