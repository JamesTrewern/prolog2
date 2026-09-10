use std::{
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

use smallvec::SmallVec;

use crate::heap::{Heap, VarBind::*};

use super::clause::Clause;

/// Constraint set for existentially quantified variables in a learned clause.
pub type Constraints = SmallVec<[usize; 5]>;

static PRED_N: AtomicUsize = AtomicUsize::new(0);

/// A collection of learned clauses produced during proof search.
///
/// During MIL resolution, when a second-order clause matches a goal,
/// a new first-order clause is invented and added to the hypothesis.
#[derive(Clone)]
pub struct Hypothesis {
    clauses: Vec<Clause>,
    pub constraints: Vec<Constraints>,
    /// Var ids of predicate variables that name an invented predicate.
    ///
    /// A predicate variable enters this set the first time it becomes the head
    /// of a hypothesis clause. Membership changes how goals on that variable
    /// are resolved: [`Env::get_choices`] offers such a goal only meta clauses
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
            clauses: Vec::new(),
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
    /// [`Env::get_choices`] and pick up the background facts.
    pub fn is_invented_pred(&self, heap: &impl Heap, var_id: usize) -> bool {
        self.invented_preds
            .iter()
            .any(|&v| matches!(heap.var_deref(v), Var(rep) if rep == var_id))
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

    /// Is this clause headed by an invented predicate?
    ///
    /// Used to withhold the clause from goals on known predicates. Such a goal
    /// unifies its constant functor with the clause's variable head, binding
    /// the invented predicate to the constant and rewriting every clause the
    /// invented predicate appears in — including clauses committed long
    /// before, since the hypothesis holds heap terms sharing that one
    /// variable, not immutable text.
    pub fn clause_head_is_invented(&self, heap: &impl Heap, clause: &Clause) -> bool {
        heap.pred_var(clause.head())
            .is_some_and(|var_id| self.is_invented_pred(heap, var_id))
    }

    /// Append the hypothesis to a choice set.
    ///
    /// With `protect` set, clauses headed by an invented predicate are
    /// withheld; see [`Self::clause_head_is_invented`]. Callers resolving a
    /// goal on a *variable* predicate must not use this: such a goal may
    /// legitimately be the invented predicate itself, and denying it its own
    /// clauses would make the predicate undefinable.
    pub fn extend_choices(&self, choices: &mut Vec<Clause>, heap: &impl Heap, protect: bool) {
        if protect {
            choices.extend(
                self.clauses
                    .iter()
                    .filter(|clause| !self.clause_head_is_invented(heap, clause))
                    .cloned(),
            );
        } else {
            choices.extend_from_slice(&self.clauses);
        }
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
        self.clauses.len()
    }

    pub fn push_clause(&mut self, clause: Clause, constraints: Constraints) {
        self.clauses.push(clause);
        self.constraints.push(constraints);
    }

    pub fn pop_clause(&mut self) -> Clause {
        self.constraints.pop();
        self.clauses.pop().unwrap()
    }

    pub fn to_string(&self, heap: &impl Heap) -> String {
        let mut buffer = String::new();
        for clause in &self.clauses {
            buffer += &clause.to_string(heap);
            buffer += "\n"
        }
        buffer
    }

    pub fn next_pred_id() -> usize {
        PRED_N.fetch_add(1, Relaxed)
    }

    pub fn invented_pred_count(&self) -> usize {
        self.invented_preds.len()
    }
}

#[cfg(test)]
mod invented_pred_tests {
    use super::*;
    use crate::heap::{QueryHeap, SymbolDB, Tag::*, VarBind::Var, VarReg};

    /// A heap holding two unary clause heads:
    ///
    /// * address 0 — `Ref_0(a)`, a head on a predicate *variable*
    /// * address 3 — `p(a)`, a head on a predicate *constant*
    ///
    /// Returns the heap plus the two clauses. `var_count` unbound variable
    /// registers are created so tests can alias them.
    fn heap_with_two_heads(var_count: usize) -> (QueryHeap<'static>, Clause, Clause) {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.cells = vec![(Comp, 2), (Ref, 0), (Con, a), (Comp, 2), (Con, p), (Con, a)];
        heap.var_regs = vec![VarReg::UNBOUND; var_count];
        (
            heap,
            Clause::new(vec![0], None, 0),
            Clause::new(vec![3], None, 0),
        )
    }

    #[test]
    fn only_the_variable_headed_clause_counts_as_invented() {
        let (heap, var_headed, con_headed) = heap_with_two_heads(1);
        let mut h = Hypothesis::new();
        assert!(h.add_invented_pred(&heap, 0));

        assert!(h.clause_head_is_invented(&heap, &var_headed));
        assert!(!h.clause_head_is_invented(&heap, &con_headed));
    }

    #[test]
    fn a_variable_head_that_was_never_invented_is_not_protected() {
        // A predicate variable only becomes invented by heading a hypothesis
        // clause. One that never did is an ordinary second-order variable and
        // must stay visible to goals on known predicates.
        let (heap, var_headed, _) = heap_with_two_heads(1);
        let h = Hypothesis::new();
        assert!(!h.clause_head_is_invented(&heap, &var_headed));
    }

    #[test]
    fn protection_withholds_invented_headed_clauses_and_keeps_the_rest() {
        let (heap, var_headed, con_headed) = heap_with_two_heads(1);
        let mut h = Hypothesis::new();
        h.push_clause(var_headed, Constraints::new());
        h.push_clause(con_headed, Constraints::new());
        h.add_invented_pred(&heap, 0);

        let mut protected = Vec::new();
        h.extend_choices(&mut protected, &heap, true);
        assert_eq!(
            protected.len(),
            1,
            "the invented-headed clause should be withheld"
        );
        assert_eq!(protected[0].head(), 3, "the constant-headed clause remains");

        let mut unprotected = Vec::new();
        h.extend_choices(&mut unprotected, &heap, false);
        assert_eq!(
            unprotected.len(),
            2,
            "with protection off the whole hypothesis is offered"
        );
    }

    #[test]
    fn protection_follows_variable_aliases() {
        // Unifying two predicate variables aliases one to the other. A clause
        // reached through the alias names the same invented predicate, so
        // comparing raw ids would let it slip through the filter.
        let (mut heap, _, _) = heap_with_two_heads(2);
        // The clause head at address 0 now reads Ref_1, which derefs to var 0.
        heap.cells[1] = (Ref, 1);
        heap.var_regs[1] = Var(0).into();
        let aliased_head = Clause::new(vec![0], None, 0);

        let mut h = Hypothesis::new();
        h.add_invented_pred(&heap, 0);
        h.push_clause(aliased_head, Constraints::new());

        assert!(
            h.clause_head_is_invented(&heap, &h[0]),
            "var 1 aliases var 0, which is invented"
        );
        let mut choices = Vec::new();
        h.extend_choices(&mut choices, &heap, true);
        assert!(choices.is_empty(), "the aliased clause must be withheld");
    }

    #[test]
    fn re_registering_an_aliased_variable_is_a_no_op() {
        let (mut heap, _, _) = heap_with_two_heads(2);
        heap.var_regs[1] = Var(0).into();

        let mut h = Hypothesis::new();
        assert!(h.add_invented_pred(&heap, 0));
        assert!(
            !h.add_invented_pred(&heap, 0),
            "the same variable must not be recorded twice"
        );
        assert_eq!(h.invented_pred_count(), 1);
    }
}

impl Deref for Hypothesis {
    type Target = Vec<Clause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for Hypothesis {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}
