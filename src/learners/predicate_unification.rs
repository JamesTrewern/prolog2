use std::{
    cmp::Ordering::{self, *},
    collections::{HashMap, HashSet},
    ops::{Deref, Range},
};

use smallvec::SmallVec;

use crate::{
    heap::{Heap, QueryHeap, SymbolDB, Tag::*, TermWalk, VarBind::Addr, Walk},
    program::{clause::Clause, hypothesis::Hypothesis},
    resolution::unify,
    utils::{BitFlag16, DirGraph8, FindReturn},
};

/// Describe the structure of a clause by the size of it's literals in order
#[derive(Debug, PartialOrd, PartialEq, Eq)]
struct ClauseSignature(Box<[usize]>);

impl ClauseSignature {
    pub fn extract_clause_signature(clause: &Clause, heap: &impl Heap) -> Self {
        Self(
            clause
                .iter()
                .map(|literal_addr| {
                    if let (Comp, len) = heap[*literal_addr] {
                        len
                    } else {
                        panic!("Malformed clause, can't extract signature")
                    }
                })
                .collect(),
        )
    }
}

impl Deref for ClauseSignature {
    type Target = Box<[usize]>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Ord for ClauseSignature {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.len().cmp(&other.len()) {
            Equal => {
                for (len1, len2) in self.iter().zip(other.iter()) {
                    match len1.cmp(len2) {
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

#[derive(Debug)]
pub struct PredDef {
    clauses: SmallVec<[Clause; 4]>,
    signatures: Vec<ClauseSignature>,
    // symbol: usize, //Con id for invented symbol
}

/// Order clauses by length
/// Break ties by comparing length of literals in order
fn cmp_clause(a: &Clause, b: &Clause, heap: &impl Heap) -> Ordering {
    match a.len().cmp(&b.len()) {
        ordering => ordering,
        Equal => {
            let len = a.len();
            for i in 0..len {
                let (_, arr1) = heap[a[i]];
                let (_, arr2) = heap[b[i]];
                match arr1.cmp(&arr2) {
                    Equal => continue,
                    ordering => return ordering,
                }
            }
            Equal
        }
    }
}

impl PredDef {
    /// Take clauses to form new predicate definition (orders clauses)
    pub fn new(heap: &impl Heap, clauses: SmallVec<[Clause; 4]>) -> Self {
        // TODO consider extra if memory allocation is slower than using cmp_clauses
        // then getting clause defintions
        // TODO? after safety guards to ensure no ref cells in literal arguments

        // Create clause signatures
        let mut clauses_signatures: Vec<(Clause, ClauseSignature)> = clauses
            .into_iter()
            .map(|clause| {
                let cs = ClauseSignature::extract_clause_signature(&clause, heap);
                (clause, cs)
            })
            .collect();
        // Order clauses by signature
        clauses_signatures.sort_by(|(_, a), (_, b)| a.cmp(b));
        // Unzip
        let (clauses, signatures) = clauses_signatures.into_iter().unzip();
        Self {
            clauses,
            signatures,
        }
    }

    /// Update variable predicates in predicate defintion
    /// to a newly coined constant predicate symbol
    pub fn make_const(&mut self, heap: &mut impl Heap, next_id: &mut usize) {
        // Extract var pred in clause heads
        let mut var_pred_ids: HashMap<usize, usize> = HashMap::new(); // Map from var_id to new const id

        // Make const all head predicates in definition
        for clause in &self.clauses {
            let (Ref, var_id) = heap[clause.head() + 1] else {
                panic!("Predicate definition is already constant")
            };
            match var_pred_ids.get(&var_id) {
                Some(pred_symbol) => heap[clause.head() + 1] = (Con, *pred_symbol),
                None => {
                    let pred_symbol = SymbolDB::set_const(format!("pred_{next_id}"));
                    *next_id += 1;
                    var_pred_ids.insert(var_id, pred_symbol);
                    heap[clause.head() + 1] = (Con, pred_symbol);
                    heap.bind(var_id, Addr(clause.head() + 1));
                }
            }
        }

        // Make const instances of head predicates in body literals
        for clause in &self.clauses {
            for literal in clause.body() {
                let (Ref, var_id) = heap[literal + 1] else {
                    continue;
                };
                if let Some(pred_symbol) = var_pred_ids.get(&var_id) {
                    heap[literal + 1] = (Con, *pred_symbol)
                }
            }
        }
    }

    /// Attempt to unify two clause definitions
    /// Self should be constant
    /// will update variable bindings on heap effecting other variable clause defintions waiting to unify
    pub fn unify(&self, var_pred_def: &PredDef, heap: &mut QueryHeap) -> bool {
        // TODO? consider if comparing signatures is needed as
        // table uses signatures to create matching range already
        // if *self.signatures != *var_pred_def.signatures {
        //     return false;
        // }
        let mut bound_vars = Vec::new();
        for (c1, c2) in self.clauses.iter().zip(var_pred_def.clauses.iter()) {
            for (&l1, &l2) in c1.iter().zip(c2.iter()) {
                match unify(heap, l1, l2, 15) {
                    Some(subs) => {
                        bound_vars.extend(subs.bound_vars);
                    }
                    None => {
                        // Ensure unbinding on failure
                        heap.unbind(&bound_vars);
                        return false;
                    }
                }
            }
        }

        true
    }

    pub fn cmp(&self, other: &Self) -> Ordering {
        match self.signatures.len().cmp(&other.signatures.len()) {
            Equal => {
                for (sig1, sig2) in self.signatures.iter().zip(other.signatures.iter()) {
                    match sig1.cmp(sig2) {
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

#[derive(Default, Debug)]
struct PredDefTable {
    pred_defs: Vec<PredDef>,
    next_id: usize,
}

impl PredDefTable {
    pub fn len(&self) -> usize {
        self.pred_defs.len()
    }

    pub fn insert(&mut self, pred_def: PredDef, heap: &mut QueryHeap) {
        match self.binary_search(&pred_def, heap) {
            FindReturn::InsertPos(insert_pos) => self.add_def(pred_def, insert_pos, heap),
            FindReturn::Index(i) => {
                let matching_range = self.find_matching_signature_range(&pred_def, heap, i);
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

    fn binary_search(&self, pred_def: &PredDef, heap: &impl Heap) -> FindReturn {
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

    fn find_matching_signature_range(
        &self,
        pred_def: &PredDef,
        heap: &impl Heap,
        i: usize,
    ) -> Range<usize> {
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

    fn print_defs(&self, heap: &impl Heap) {
        for (i, pred_def) in self.pred_defs.iter().enumerate() {
            println!("====== Definition {i} ======");
            for clause in &pred_def.clauses {
                println!("{}", clause.to_string(heap))
            }
            println!("===========================");
        }
    }

    pub fn extract_pred_defs_from_h(&mut self, hypothesis: &mut Hypothesis, heap: &mut QueryHeap) {
        let mut clause_sets: Vec<SmallVec<[Clause; 4]>> = Vec::with_capacity(hypothesis.len());
        let mut var_preds = Vec::with_capacity(hypothesis.len());
        let mut dependencies: Vec<HashSet<usize>> = Vec::with_capacity(hypothesis.len());

        for idx in (0..hypothesis.len()).rev() {
            if let (Ref, var_id) = heap.get_deref_cell(hypothesis[idx].head() + 1) {
                let clause = hypothesis.remove(idx);
                match var_preds.iter().position(|var_pred| *var_pred == var_id) {
                    Some(def_index) => {
                        extract_body_var_preds(&mut dependencies[def_index], &clause, heap);
                        clause_sets[def_index].push(clause);
                    }
                    None => {
                        var_preds.push(var_id);
                        let mut body_var_preds = HashSet::new();
                        extract_body_var_preds(&mut body_var_preds, &clause, heap);
                        dependencies.push(body_var_preds);
                        clause_sets.push(SmallVec::from_elem(clause, 1));
                    }
                }
            }
        }

        // Build dependency graph
        // find SCCs
        // merge SCCs into 1 pred def
        // use new dependency graph to order pred defs
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
                for group in &groups[..groups.size] {
                    let mut clauses: SmallVec<[Clause; 4]> = SmallVec::new();
                    for i in 0..graph.size {
                        if group & 1 << i != 0 {
                            clauses.append(&mut clause_sets[i]);
                        }
                    }
                    self.insert(PredDef::new(heap, clauses), heap);
                }
            } else {
                let order = graph.order();
                //TODO avoid cloning here
                for &idx in &order[..graph.size] {
                    self.insert(PredDef::new(heap, clause_sets[idx].clone()), heap);
                }
            }
        } else {
            todo!("Can't handle sub hypotheses greater than 8 clauses")
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

fn extract_pred_defs_from_h(hypothesis: &mut Hypothesis, heap: &impl Heap) -> Vec<PredDef> {
    // TODO clause sets as small vec of clause indexes

    let mut clause_sets: Vec<SmallVec<[Clause; 4]>> = Vec::with_capacity(hypothesis.len());
    let mut var_preds = Vec::with_capacity(hypothesis.len());
    let mut dependencies: Vec<HashSet<usize>> = Vec::with_capacity(hypothesis.len());

    for idx in (0..hypothesis.len()).rev() {
        if let (Ref, var_id) = heap.get_deref_cell(hypothesis[idx].head() + 1) {
            let clause = hypothesis.remove(idx);
            match var_preds.iter().position(|var_pred| *var_pred == var_id) {
                Some(def_index) => {
                    extract_body_var_preds(&mut dependencies[def_index], &clause, heap);
                    clause_sets[def_index].push(clause);
                }
                None => {
                    var_preds.push(var_id);
                    let mut body_var_preds = HashSet::new();
                    extract_body_var_preds(&mut body_var_preds, &clause, heap);
                    dependencies.push(body_var_preds);
                    clause_sets.push(SmallVec::from_elem(clause, 1));
                }
            }
        }
    }

    // Build dependency graph
    // find SCCs
    // merge SCCs into 1 pred def
    // use new dependency graph to order pred defs
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
            let mut pred_defs: Vec<PredDef> = Vec::with_capacity(groups.size);
            for group in groups.iter() {
                let mut clauses: SmallVec<[Clause; 4]> = SmallVec::new();
                for i in 0..groups.size {
                    if group & 1 << i != 0 {
                        clauses.append(&mut clause_sets[i]);
                    }
                }
                pred_defs.push(PredDef::new(heap, clauses));
            }
            pred_defs
        } else {
            let order = graph.order();
            //TODO avoid cloning here
            order
                .into_iter()
                .map(|i| PredDef::new(heap, clause_sets[i].clone()))
                .collect()
        }
    } else {
        todo!("Can't handle sub hypotheses greater than 8 clauses")
    }
}

#[cfg(test)]
mod tests {
    use smallvec::SmallVec;

    use crate::{
        heap::{
            Cell, Heap, QueryHeap, SymbolDB,
            Tag::*,
            VarBind::{self, *},
            VarReg,
        },
        learners::predicate_unification::{extract_pred_defs_from_h, PredDef, PredDefTable},
        parser::{_build_clause, execute_tree, tokenise, TokenStream},
        program::{
            clause::Clause,
            hypothesis::{Constraints, Hypothesis},
            predicate_table::PredicateTable,
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

    fn push_literal(heap: &mut QueryHeap, sub_terms: &[Cell]) -> usize {
        let addr = heap.heap_push((Comp, sub_terms.len()));
        heap.cells.extend_from_slice(&sub_terms);
        addr
    }

    fn instantiate_meta_rule(
        heap: &mut QueryHeap,
        meta: &Clause,
        bindings: &[(usize, VarBind)],
    ) -> Clause {
        let mut subs = Substitution::new(15);
        for (arg_id, binding) in bindings {
            subs.set_arg(*arg_id, *binding);
        }

        let new_clause_literals: Vec<usize> = meta
            .iter()
            .map(|literal| build(heap, &mut subs, Some(meta.meta_vars), *literal))
            .collect();

        Clause::new(new_clause_literals, None, meta.max_arg_id)
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
            h.push_clause(
                instantiate_meta_rule(heap, meta_rule, &bindings),
                Constraints::default(),
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
        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);

        pdt.print_defs(&heap);

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

        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);

        pdt.print_defs(&heap);

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
        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);
        pdt.print_defs(&heap);

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
        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);
        pdt.print_defs(&heap);

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
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));
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
        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);
        pdt.print_defs(&heap);

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
        pdt.extract_pred_defs_from_h(&mut h1, &mut heap);
        pdt.extract_pred_defs_from_h(&mut h2, &mut heap);
        pdt.print_defs(&heap);

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
