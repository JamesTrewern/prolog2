use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use smallvec::SmallVec;

use crate::{
    heap::{ArgRegs, Heap, VarBind::*, VarReg},
    resolution::{build, Substitution},
    CONSTRAINTS_DEFAULT_SIZE,
};

use super::{Clause, MetaSub, MetaSubTrait, PredicateTable};

/// Constraint set for existentially quantified variables in a learned clause.
pub(crate) type Constraints = SmallVec<[usize; CONSTRAINTS_DEFAULT_SIZE]>;

static PRED_N: AtomicUsize = AtomicUsize::new(0);

/// A collection of learned clauses produced during proof search.
///
/// During MIL resolution, when a second-order clause matches a goal,
/// a new first-order clause is invented and added to the hypothesis.
///
/// A clause is held as a `MetaSub` -- the meta clause it instantiates and
/// the bindings of that clause's meta variables -- and never built.
#[derive(Clone)]
pub struct Hypothesis {
    pub meta_subs: Vec<MetaSub>,
    pub constraints: Vec<Constraints>,
    /// Var ids of predicate variables that name an invented predicate.
    ///
    /// A predicate variable enters this set the first time it becomes the head
    /// of a hypothesis clause. Membership changes how goals on that variable
    /// are resolved: `Env::get_choices` offers such a goal only meta clauses
    /// and existing hypothesis clauses, never background facts, which is what
    /// forces the search to *define* the predicate rather than alias it to a
    /// background relation.
    ///
    /// Held as a `Vec` rather than a set because entries are removed on
    /// backtracking; the [`Env`] that added an id records it so that undoing
    /// removes the right one.
    invented_preds: Vec<usize>,
}

impl Hypothesis {
    pub fn new() -> Self {
        Hypothesis {
            meta_subs: Vec::new(),
            constraints: Vec::new(),
            invented_preds: Vec::new(),
        }
    }

    /// Is this predicate variable the head of an invented predicate?
    ///
    /// Compared modulo dereference: unification of two predicate variables
    /// aliases one to the other, so the id recorded at invention time and the
    /// id a later goal presents may differ while naming the same predicate.
    /// Comparing raw ids would let an aliased goal escape the gate in
    /// `Env::get_choices` and pick up the background facts.
    pub fn is_invented_pred(&self, heap: &impl Heap, var_id: usize) -> bool {
        self.invented_preds
            .iter()
            .any(|&v| matches!(heap.var_deref(v), VarId(rep) if rep == var_id))
    }

    /// Record `var_id` as an invented predicate.
    ///
    /// Returns `false` if it already names one, in which case the caller has
    /// resolved against an existing invented predicate rather than creating a
    /// new one and must not record anything to undo.
    pub fn add_invented_pred(&mut self, heap: &impl Heap, var_id: usize) -> bool {
        if self.is_invented_pred(heap, var_id) {
            return false;
        }
        self.invented_preds.push(var_id);
        true
    }

    /// Undo a previous [`Self::add_invented_pred`].
    pub fn remove_invented_pred(&mut self, var_id: usize) {
        debug_assert_eq!(
            self.invented_preds.last(),
            Some(&var_id),
            "invented predicates must be removed in reverse order of addition"
        );
        if let Some(i) = self.invented_preds.iter().rposition(|&v| v == var_id) {
            self.invented_preds.remove(i);
        }
    }

    pub fn len(&self) -> usize {
        self.meta_subs.len()
    }

    /// Record the clause the registers `arg_regs` make of the meta clause
    /// `template`, which sits at `clause_idx` in the predicate table.
    pub fn push_clause(
        &mut self,
        template: &Clause,
        clause_idx: usize,
        constraints: Constraints,
        arg_regs: &ArgRegs,
    ) {
        let threshold = template
            .meta_threshold()
            .expect("a hypothesis clause instantiates a meta clause");
        self.constraints.push(constraints);
        self.meta_subs.push(MetaSub::from_arg_regs(
            arg_regs,
            clause_idx,
            threshold,
            template.max_arg_id,
        ));
    }

    pub fn pop_clause(&mut self) {
        self.constraints.pop();
        self.meta_subs.pop();
    }

    /// The clauses as text, one per line. Each is built onto `heap` to be
    /// printed, and the heap is then put back as it was.
    pub fn to_string(&self, heap: &mut impl Heap, predicate_table: &PredicateTable) -> String {
        HypothesisTrait::to_string(self, heap, predicate_table)
    }

    /// As [`Self::to_string`], one string per clause.
    pub fn clause_strings(
        &self,
        heap: &mut impl Heap,
        predicate_table: &PredicateTable,
    ) -> Vec<String> {
        HypothesisTrait::clause_strings(self, heap, predicate_table)
    }

    pub fn next_pred_id() -> usize {
        PRED_N.fetch_add(1, Relaxed)
    }

    pub fn invented_pred_count(&self) -> usize {
        self.invented_preds.len()
    }
}

/// What native predicates are handed by a proof whose hypothesis is not a
/// [`Hypothesis`].
static EMPTY: Hypothesis = Hypothesis {
    meta_subs: Vec::new(),
    constraints: Vec::new(),
    invented_preds: Vec::new(),
};

/// The clauses a [`Proof`](crate::resolution::Proof) resolves goals against
/// besides the program's own, in whichever form they are held:
///
/// * [`Hypothesis`] -- the proof learns: it may add clauses.
/// * `&Hypothesis` -- read only, for testing a hypothesis that is not
///   ground and so still needs its constraints and invented predicates.
/// * `&[&[usize]]` -- ground clauses as packed `MetaSub`s
///   (`[clause_idx, subs...]`); read only.
/// * `&[Clause]` -- ground clauses already built; read only.
///
/// A clause is resolved through its *template*: the meta clause it
/// instantiates, with the meta variables' registers loaded from its
/// substitutions, or the clause itself when it is held built.
pub(crate) trait HypothesisTrait {
    /// Whether a proof over this may add clauses to it. The methods below
    /// the line are only called when it may.
    const LEARNS: bool = false;

    fn len(&self) -> usize;

    /// The clause that clause `index` is resolved through. A `MetaSub`'s
    /// index must be good for `predicate_table`.
    fn template<'t>(&'t self, index: usize, predicate_table: &'t PredicateTable) -> &'t Clause;

    /// Load clause `index`'s substitutions into `meta_regs`, the registers
    /// of its template's meta variables. Only called for a meta template.
    fn load_subs(&self, index: usize, meta_regs: &mut [VarReg]);

    fn constraints(&self) -> &[Constraints] {
        &[]
    }

    fn is_invented_pred(&self, _heap: &impl Heap, _var_id: usize) -> bool {
        false
    }

    /// The hypothesis native predicates see.
    fn learned(&self) -> &Hypothesis {
        &EMPTY
    }

    /// Each clause as text. A clause held as a `MetaSub` is built onto
    /// `heap` to be printed, and the heap is then put back as it was; for
    /// reporting and debug output.
    fn clause_strings(
        &self,
        heap: &mut impl Heap,
        predicate_table: &PredicateTable,
    ) -> Vec<String> {
        let heap_point = heap.heap_point();
        let strings = (0..self.len())
            .map(|index| {
                let template = self.template(index, predicate_table);
                let Some(threshold) = template.meta_threshold() else {
                    return template.to_string(heap);
                };
                let mut substitution = Substitution::new(template.max_arg_id);
                let meta_regs = &mut substitution.arg_regs[threshold..template.max_arg_id];
                self.load_subs(index, meta_regs);
                let literals = template
                    .iter()
                    .map(|&literal| build(heap, &mut substitution, Some(threshold), literal))
                    .collect();
                Clause::new(literals, None, template.max_arg_id).to_string(heap)
            })
            .collect();
        heap.truncate(heap_point);
        strings
    }

    /// [`Self::clause_strings`], one per line.
    fn to_string(&self, heap: &mut impl Heap, predicate_table: &PredicateTable) -> String {
        self.clause_strings(heap, predicate_table).join("\n")
    }

    // ── learning only ───────────────────────────────────────────────────

    fn add_invented_pred(&mut self, _heap: &impl Heap, _var_id: usize) -> bool {
        unreachable!("only a learning hypothesis invents predicates")
    }

    fn remove_invented_pred(&mut self, _var_id: usize) {
        unreachable!("only a learning hypothesis invents predicates")
    }

    fn push_clause(
        &mut self,
        _template: &Clause,
        _clause_idx: usize,
        _constraints: Constraints,
        _arg_regs: &ArgRegs,
    ) {
        unreachable!("only a learning hypothesis is added to")
    }

    fn pop_clause(&mut self) {
        unreachable!("only a learning hypothesis is added to")
    }
}

impl HypothesisTrait for Hypothesis {
    const LEARNS: bool = true;

    fn len(&self) -> usize {
        self.meta_subs.len()
    }

    fn template<'t>(&'t self, index: usize, predicate_table: &'t PredicateTable) -> &'t Clause {
        self.meta_subs[index].template(predicate_table)
    }

    fn load_subs(&self, index: usize, meta_regs: &mut [VarReg]) {
        meta_regs.copy_from_slice(&self.meta_subs[index].subs);
    }

    fn constraints(&self) -> &[Constraints] {
        &self.constraints
    }

    fn is_invented_pred(&self, heap: &impl Heap, var_id: usize) -> bool {
        Hypothesis::is_invented_pred(self, heap, var_id)
    }

    fn learned(&self) -> &Hypothesis {
        self
    }

    fn add_invented_pred(&mut self, heap: &impl Heap, var_id: usize) -> bool {
        Hypothesis::add_invented_pred(self, heap, var_id)
    }

    fn remove_invented_pred(&mut self, var_id: usize) {
        Hypothesis::remove_invented_pred(self, var_id)
    }

    fn push_clause(
        &mut self,
        template: &Clause,
        clause_idx: usize,
        constraints: Constraints,
        arg_regs: &ArgRegs,
    ) {
        Hypothesis::push_clause(self, template, clause_idx, constraints, arg_regs)
    }

    fn pop_clause(&mut self) {
        Hypothesis::pop_clause(self);
    }
}

impl HypothesisTrait for &Hypothesis {
    fn len(&self) -> usize {
        self.meta_subs.len()
    }

    fn template<'t>(&'t self, index: usize, predicate_table: &'t PredicateTable) -> &'t Clause {
        self.meta_subs[index].template(predicate_table)
    }

    fn load_subs(&self, index: usize, meta_regs: &mut [VarReg]) {
        meta_regs.copy_from_slice(&self.meta_subs[index].subs);
    }

    fn constraints(&self) -> &[Constraints] {
        &self.constraints
    }

    fn is_invented_pred(&self, heap: &impl Heap, var_id: usize) -> bool {
        Hypothesis::is_invented_pred(self, heap, var_id)
    }

    fn learned(&self) -> &Hypothesis {
        self
    }
}

impl HypothesisTrait for &[&[usize]] {
    fn len(&self) -> usize {
        <[_]>::len(self)
    }

    fn template<'t>(&'t self, index: usize, predicate_table: &'t PredicateTable) -> &'t Clause {
        self[index].template(predicate_table)
    }

    fn load_subs(&self, index: usize, meta_regs: &mut [VarReg]) {
        let subs = &self[index][1..];
        debug_assert_eq!(subs.len(), meta_regs.len());
        for (reg, &sub) in meta_regs.iter_mut().zip(subs) {
            *reg = VarReg(sub);
        }
    }
}

impl HypothesisTrait for &[Clause] {
    fn len(&self) -> usize {
        <[_]>::len(self)
    }

    fn template<'t>(&'t self, index: usize, _: &'t PredicateTable) -> &'t Clause {
        &self[index]
    }

    fn load_subs(&self, _: usize, _: &mut [VarReg]) {}
}

#[cfg(test)]
mod invented_pred_tests {
    use super::*;
    use crate::heap::{test_prog, QueryHeap, VarBind::VarId, VarReg};

    #[test]
    fn invented_predicates_are_compared_through_aliases() {
        // Unifying two predicate variables aliases one to the other, so
        // either id names the invented predicate.
        let mut heap = QueryHeap::new(test_prog(), None);
        heap.var_regs = vec![VarReg::UNBOUND; 3];
        heap.var_regs[1] = VarId(0).into();

        let mut h = Hypothesis::new();
        assert!(h.add_invented_pred(&heap, 1));
        assert!(h.is_invented_pred(&heap, 0));
        assert!(!h.is_invented_pred(&heap, 2));
    }

    #[test]
    fn re_registering_an_aliased_variable_is_a_no_op() {
        let mut heap = QueryHeap::new(test_prog(), None);
        heap.var_regs = vec![VarReg::UNBOUND; 2];
        heap.var_regs[1] = VarId(0).into();

        let mut h = Hypothesis::new();
        assert!(h.add_invented_pred(&heap, 0));
        assert!(
            !h.add_invented_pred(&heap, 0),
            "the same variable must not be recorded twice"
        );
        assert_eq!(h.invented_pred_count(), 1);
    }
}
