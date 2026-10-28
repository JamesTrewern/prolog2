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
        VarBind::{Addr, Var},
        VarReg,
    },
    program::{clause::Clause, meta_sub::MetaSub},
    utils::{DirGraph8, FindReturn},
};

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

    /// Update variable predicates in predicate defintion
    /// to a newly coined constant predicate symbol
    pub fn make_const(&mut self, heap: &mut impl Heap, next_id: &mut usize) {
        // Extract var pred in clause heads
        let mut var_pred_ids: HashMap<usize, VarReg> = HashMap::new(); // Map from var_id to new const id

        //coin new const for all vars in metasubs
        for meta_sub in self.iter_mut() {
            for var_reg in &mut meta_sub.subs {
                if let Var(var_id) = var_reg.get_bind().unwrap() {
                    match heap.var_deref(var_id) {
                        Var(var_id) => {
                            match var_pred_ids.get(&var_id) {
                                Some(new_reg_value) => *var_reg = *new_reg_value, //Var bound in previous meta_sub
                                None => {
                                    let pred_symbol =
                                        SymbolDB::set_const(format!("pred_{next_id}"));
                                    let addr = heap.heap_push((Con, pred_symbol));
                                    var_pred_ids.insert(var_id, Addr(addr).into());
                                    *next_id += 1;
                                    heap.bind(var_id, Addr(addr));
                                    *var_reg = Addr(addr).into()
                                }
                            }
                        }
                        value => *var_reg = value.into(),
                    }
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
            if let (Ref, var_id) = heap.get_deref_cell(clauses[idx].head() + 1) {
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

        if clause_sets.len() <= 8 {
            let mut graph: DirGraph8 = DirGraph8::new(clause_sets.len());
            for (i, deps) in dependencies.into_iter().enumerate() {
                for dep in deps {
                    graph.add_edge(
                        i,
                        var_preds
                            .iter()
                            .position(|var_pred| *var_pred == dep)
                            .unwrap(),
                    );
                }
            }
            if let Some(groups) = graph.ordered_cyclic_groups() {
                groups[..groups.size]
                    .into_iter()
                    .map(|group| {
                        let mut meta_subs: SmallVec<[MetaSub; 4]> = SmallVec::new();
                        for i in 0..graph.size {
                            if group & 1 << i != 0 {
                                meta_subs.extend(clause_sets[i].drain(..).map(|(_, msub)| msub));
                            }
                        }
                        PredDef::new(meta_subs)
                    })
                    .collect()
            } else {
                graph.order()[..graph.size]
                    .iter()
                    .map(|i| {
                        PredDef::new(clause_sets[*i].drain(..).map(|(_, msub)| msub).collect())
                    })
                    .collect()
            }
        } else {
            todo!("Can't handle sub hypotheses greater than 8 clauses")
        }
    }
}

#[derive(Default, Debug)]
pub struct PredDefTable {
    pub pred_defs: Vec<PredDef>,
    pub next_id: usize,
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

    fn add_def(&mut self, mut pred_def: PredDef, insert_pos: usize, heap: &mut QueryHeap) {
        pred_def.make_const(heap, &mut self.next_id);
        self.next_id += 1;
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
                        Some(Var(var_id)) => format!("Var_{var_id}"),
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
        if let (Ref, var_id) = heap.get_deref_cell(literal + 1) {
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
        learners::predicate_unification::PredDefTable,
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
                if let Var(var_id) = bind {
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
            [(0, &[Addr(p), Var(0)]), (1, &[Var(0), Addr(q), Addr(r)])],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [(0, &[Addr(p), Var(1)]), (1, &[Var(1), Addr(q), Addr(r)])],
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
                (0, &[Addr(p), Var(0)]),
                (1, &[Var(0), Addr(q), Addr(r)]),
                (1, &[Var(0), Addr(r), Addr(q)]),
            ],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), Var(1)]),
                (1, &[Var(1), Addr(q), Addr(r)]),
                (1, &[Var(1), Addr(r), Addr(q)]),
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
                (0, &[Addr(p), Var(0)]),
                (0, &[Var(0), Var(1)]),
                (1, &[Var(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );

        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), Var(2)]),
                (0, &[Var(2), Var(3)]),
                (1, &[Var(3), Addr(q), Addr(r)]),
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
                (0, &[Addr(p), Var(0)]),
                (0, &[Var(0), Var(1)]),
                (0, &[Var(0), Addr(p)]),
                (1, &[Var(1), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), Var(2)]),
                (0, &[Var(2), Var(3)]),
                (1, &[Var(3), Addr(q), Addr(r)]),
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
                (0, &[Addr(p), Var(0)]),
                (0, &[Var(0), Var(1)]),
                (0, &[Var(1), Var(0)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), Var(2)]),
                (0, &[Var(2), Var(3)]),
                (0, &[Var(3), Var(2)]),
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
                (0, &[Addr(p), Var(0)]),
                (0, &[Var(0), Var(1)]),
                (0, &[Var(0), Var(2)]),
                (0, &[Var(1), Var(0)]),
                (1, &[Var(2), Addr(q), Addr(r)]),
            ],
            &mut heap,
        );
        let mut h2 = build_hypothesis(
            meta_rules,
            [
                (0, &[Addr(p), Var(0)]),
                (0, &[Var(3), Var(4)]),
                (0, &[Var(3), Var(5)]),
                (0, &[Var(4), Var(3)]),
                (1, &[Var(5), Addr(q), Addr(r)]),
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
