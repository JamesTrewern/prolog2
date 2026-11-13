//! Goal environment for the SLD resolution proof search.
//!
//! Each [`Env`] represents a single goal on the proof stack. The [`Strategy`]
//! enum separates clause-based resolution from native predicate evaluation,
//! keeping the two execution paths explicit at the type level.
use smallvec::SmallVec;

use crate::{
    heap::{
        ArgRegs, Heap, HeapPoint, QueryHeap, SymbolDB, Tag,
        VarBind::{self, Addr, VarId},
    },
    predicate_modules::{PredReturn, PredicateFunction},
    program::{
        HypothesisTrait, {BitFlag64, Clause, MAX_ARG}, {PredicateRef, PredicateTable},
    },
    resolution::{
        build::{build, re_build_bound_arg_terms},
        choices::Choices,
        constraints::pre_pass_constraint,
        unification::{unify, unify_from},
        Substitution,
    },
    Bindings, Config,
};
/// How a goal is resolved: either by unifying with clauses or by calling a
/// native predicate function.
#[derive(Debug)]
pub(crate) enum Strategy<'a> {
    /// Resolution via clause unification (standard SLD + meta-interpretive learning).
    Clause {
        choices: Choices<'a>,
        /// Whether a hypothesis clause was added on the last successful try.
        new_clause: bool,
        /// Var id of the predicate variable that this env registered as an
        /// invented predicate on the last successful try, if any. Held so that
        /// [`Env::undo_try`] removes exactly the entry this env added rather
        /// than relying on the hypothesis' invented set unwinding in step with
        /// the env stack.
        invent_pred: Option<usize>,
    },
    /// Resolution via a native predicate function, with optional backtrackable
    /// alternatives produced by [`PredReturn::Choices`].
    Native {
        function: PredicateFunction,
        /// Alternative results to try on backtracking. Each entry is a
        /// `(bindings, sub_goals)` pair, popped one at a time.
        alternatives: Vec<(Vec<(usize, VarBind)>, Vec<usize>)>,
        /// Whether the predicate function has been called yet.
        called: bool,
    },
    Conjunction {
        goals: Vec<usize>,
        expanded: bool,
    },
    Unset,
}

/// A goal environment in the proof search.
///
/// Shared fields live directly on the struct; the divergent clause-vs-native
/// state lives inside [`Strategy`].
#[derive(Debug)]
pub(super) struct Env<'a> {
    pub(super) goal: usize,
    /// The variables this env's successful try bound, undone when it is
    /// retried or backtracked past.
    ///
    /// Inline rather than `Box<[usize]>`: 84% of successful unifications
    /// bind nothing and 99% bind at most one, so boxing cost an allocation
    /// per accepted clause to hold almost always nothing.
    pub(super) bound_vars: Bindings,
    pub(super) children: usize,
    pub(super) depth: usize,
    pub(crate) got_choices: bool,
    pub(super) heap_point: HeapPoint,
    pub(super) strategy: Strategy<'a>,
}

impl<'a> Env<'a> {
    pub(super) fn new(goal: usize, depth: usize, heap_point: HeapPoint) -> Env<'a> {
        Env {
            goal,
            bound_vars: Bindings::new(),
            children: 0,
            depth,
            got_choices: false,
            heap_point,
            // Default to an empty clause strategy; overwritten by get_choices.
            strategy: Strategy::Unset,
        }
    }

    // ── accessors for strategy-specific fields ──────────────────────────

    /// Whether the last successful clause try added a hypothesis clause.
    pub(super) fn new_clause(&self) -> bool {
        matches!(
            &self.strategy,
            Strategy::Clause {
                new_clause: true,
                ..
            }
        )
    }

    /// The predicate variable invented by the last successful clause try, if any.
    pub(super) fn invent_pred(&self) -> Option<usize> {
        match &self.strategy {
            Strategy::Clause { invent_pred, .. } => *invent_pred,
            _ => None,
        }
    }

    // ── choice gathering ────────────────────────────────────────────────

    /// Gather the clauses this goal may resolve against.
    ///
    /// `protect` is [`Config::protect_h_preds`]. It insulates invented
    /// predicates from the rest of the program in the two directions they can
    /// be reached from, which are separate cases needing separate treatment:
    ///
    /// * A goal *on* an invented predicate is denied the background facts,
    ///   handled in [`Self::get_choices_var_pred`].
    /// * A goal on a predicate that *has background clauses* is denied the
    ///   hypothesis clauses that an invented predicate heads, handled in
    ///   [`Self::get_choices_con_pred`].
    ///
    /// Guarding only the first is not enough. The two are not symmetric: the
    /// first asks what an invented predicate may match, the second asks what
    /// may match *it*, and a goal on a known predicate never consults the
    /// invented set at all.
    ///
    /// The second guard stops at predicates the program defines. A goal on an
    /// unknown symbol — the target predicate, which has no background clauses
    /// — always sees the whole hypothesis, since reusing learned clauses
    /// across examples is the point of resolving such a goal at all; see the
    /// `None` arm of [`Self::get_choices_con_pred`].
    pub(super) fn get_choices<H: HypothesisTrait>(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut H,
        predicate_table: &'a PredicateTable,
        protect: bool,
    ) {
        self.got_choices = true;
        self.heap_point = heap.heap_point();

        if heap[self.goal].0 == Tag::Tup {
            self.get_tup_goals(heap);
        } else {
            match heap.symbol_arity(self.goal) {
                (0, arity) => {
                    self.get_choices_var_pred(heap, hypothesis, predicate_table, arity, protect)
                }
                sym_arr => {
                    self.get_choices_con_pred(heap, hypothesis, predicate_table, sym_arr, protect)
                }
            }
        }
    }

    /// A tuple goal is a conjunction: every element has to be proved.
    ///
    /// The elements are taken as they lie on the heap rather than copied, so
    /// a nested tuple stays a tuple and becomes a conjunction of its own when
    /// [`Self::get_choices`] reaches it. An empty tuple yields no goals, which
    /// succeeds -- the empty conjunction is true.
    fn get_tup_goals(&mut self, heap: &QueryHeap) {
        self.strategy = Strategy::Conjunction {
            goals: heap.str_args(self.goal),
            expanded: false,
        }
    }

    /// Get choices for a variable predicate goal
    /// Choices is built from:
    /// hypothesis clauses, variable predicate clauses, and — unless the goal's
    /// predicate variable already names an invented predicate — body clauses.
    ///
    /// The body clauses are withheld for an invented predicate because a goal
    /// on one must be discharged by the hypothesis or by extending it, never
    /// by silently aliasing the invented predicate to a background relation.
    /// The hypothesis itself is always offered: this goal may *be* the
    /// invented predicate, and denying it its own clauses would leave the
    /// predicate undefinable.
    fn get_choices_var_pred<H: HypothesisTrait>(
        &mut self,
        heap: &QueryHeap,
        hypothesis: &mut H,
        predicate_table: &'a PredicateTable,
        arity: usize,
        protect: bool,
    ) {
        let invented = protect
            && heap
                .pred_var(self.goal)
                .is_some_and(|var_id| hypothesis.is_invented_pred(heap, var_id));

        // Variable goal — gather meta-rules and body clauses. The whole
        // hypothesis is offered unfiltered: this goal may *be* an invented
        // predicate, so the clauses defining invented predicates are exactly
        // the ones it needs.
        let mut choices = Choices::with_hypothesis(hypothesis.len())
            .var_pred(predicate_table.get_variable_clauses(arity));
        if !invented {
            choices = choices.body_preds(predicate_table.get_body_clauses(arity));
        }
        self.strategy = Strategy::Clause {
            choices,
            new_clause: false,
            invent_pred: None,
        };
    }

    /// Get choices for constant predicate goal
    /// If symbol/arity is a predicate function select Native strategy
    /// If symbol/arity is a known predicate use hashmap to get clauses + hypothesis
    /// If symbol/arity is unkown predicate get hypothesis and variable predicate clauses
    fn get_choices_con_pred<H: HypothesisTrait>(
        &mut self,
        heap: &QueryHeap,
        hypothesis: &mut H,
        predicate_table: &'a PredicateTable,
        (symbol, arity): (usize, usize),
        protect: bool,
    ) {
        match predicate_table.get_predicate((symbol, arity)) {
            Some(PredicateRef::Function(pred_function)) => {
                self.strategy = Strategy::Native {
                    function: pred_function,
                    alternatives: Vec::new(),
                    called: false,
                };
            }
            Some(PredicateRef::Clauses(clauses)) => {
                let choices = if protect {
                    Choices::with_protected_hypothesis(hypothesis.len())
                } else {
                    Choices::with_hypothesis(hypothesis.len())
                };
                self.strategy = Strategy::Clause {
                    choices: choices.known_pred(clauses),
                    new_clause: false,
                    invent_pred: None,
                };
            }
            None => {
                // Unfiltered, unlike the known-predicate branch above. An
                // unknown symbol is typically the target predicate, which by
                // definition has no background clauses, so every goal on it
                // must see the whole hypothesis: that is how a hypothesis
                // learned from the first example is reused to discharge the
                // rest. Capture of an invented predicate by the target is
                // instead left to the inequality constraints, which do cover
                // it — the target and the invented predicate appear together
                // in the constraint set of the clause that introduced them.
                self.strategy = Strategy::Clause {
                    choices: Choices::with_hypothesis(hypothesis.len())
                        .var_pred(predicate_table.get_variable_clauses(arity)),
                    new_clause: false,
                    invent_pred: None,
                };
            }
        }
    }

    // ── undo / backtrack ────────────────────────────────────────────────

    pub(super) fn undo_try<H: HypothesisTrait>(
        &mut self,
        hypothesis: &mut H,
        heap: &mut QueryHeap,
        debug: bool,
    ) -> usize {
        if debug {
            eprintln!(
                "[UNDO_TRY] goal={} addr={}",
                heap.term_string(self.goal),
                self.goal
            );
        }
        if let Strategy::Clause {
            new_clause,
            invent_pred,
            ..
        } = &mut self.strategy
        {
            if *new_clause {
                hypothesis.pop_clause();
                if debug {
                    eprintln!(
                        "[UNDO_CLAUSE|{}] {} clauses left",
                        self.depth,
                        hypothesis.len()
                    );
                }
                *new_clause = false;
                if let Some(var_id) = invent_pred.take() {
                    hypothesis.remove_invented_pred(var_id);
                }
            }
        }
        heap.unbind(&self.bound_vars);
        heap.truncate(self.heap_point);
        self.children
    }

    // ── reset on backtrack-from ─────────────────────────────────────────

    /// Reset this env when backtracking past it, so it gets fresh choices on
    /// a future visit via a different proof path.
    pub(super) fn reset(&mut self, heap: &mut QueryHeap) {
        heap.truncate(self.heap_point);
        self.got_choices = false;
        match &mut self.strategy {
            Strategy::Clause { choices, .. } => *choices = Choices::default(),
            Strategy::Native {
                called,
                alternatives,
                ..
            } => {
                *called = false;
                alternatives.clear();
            }
            Strategy::Conjunction { expanded, .. } => *expanded = false,
            Strategy::Unset => (),
        }
    }

    // ── try choices (dispatch) ──────────────────────────────────────────

    pub(super) fn try_choices<H: HypothesisTrait>(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut H,
        predicate_table: &'a PredicateTable,
        config: Config,
    ) -> Option<Vec<Env<'a>>> {
        if self.depth > config.max_depth {
            if config.debug {
                eprintln!(
                    "[FAIL_ON_DEPTH|{}] goal={}",
                    self.depth,
                    heap.term_string(self.goal),
                );
            }
            return None;
        }

        match &self.strategy {
            Strategy::Native { .. } => self.try_native(heap, hypothesis, predicate_table, config),
            Strategy::Clause { .. } => self.try_clause(
                heap,
                hypothesis,
                predicate_table,
                H::LEARNS && hypothesis.len() < config.max_clause,
                config.debug,
            ),
            Strategy::Conjunction { .. } => self.try_conj(heap),
            Strategy::Unset => unreachable!("Shouldn't be able to try choices before getting them"),
        }
    }

    // ── native predicate resolution ─────────────────────────────────────

    fn try_native<H: HypothesisTrait>(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut H,
        predicate_table: &PredicateTable,
        config: Config,
    ) -> Option<Vec<Env<'a>>> {
        let Strategy::Native {
            function,
            alternatives,
            called,
        } = &mut self.strategy
        else {
            unreachable!()
        };

        // First call: invoke the predicate function.
        if !*called {
            *called = true;
            match function(
                heap,
                hypothesis.learned(),
                self.goal,
                predicate_table,
                config,
            ) {
                PredReturn::True => return Some(Vec::new()),
                PredReturn::False => {
                    if config.debug {
                        println!("[FAILED] {}", heap.term_string(self.goal))
                    }
                    return None;
                }
                PredReturn::Success(bound_vars, goals) => {
                    self.bound_vars = bound_vars;
                    if goals.is_empty() {
                        return Some(Vec::new());
                    }
                    self.children = goals.len();
                    return Some(
                        goals
                            .into_iter()
                            .map(|g| Env::new(g, self.depth + 1, heap.heap_point()))
                            .collect(),
                    );
                }
                PredReturn::Choices(alts) => {
                    *alternatives = alts;
                    // The predicate may have built terms for its alternatives
                    // to bind to, and those have to outlive the undo:
                    self.heap_point = heap.heap_point();
                }
            }
        }

        // Pop the next alternative (either from initial Choices or on backtrack).
        let Strategy::Native { alternatives, .. } = &mut self.strategy else {
            unreachable!()
        };
        let (bindings, goals) = alternatives.pop()?;
        let mut bound_vars = Bindings::with_capacity(bindings.len());
        for (var_id, binding) in bindings {
            bound_vars.push(var_id);
            heap.bind(var_id, binding);
        }
        // Recorded so `undo_try` unbinds them before the next alternative is
        // tried; without this the second attempt would bind an already-bound
        // variable.
        self.bound_vars = bound_vars;
        if goals.is_empty() {
            Some(Vec::new())
        } else {
            self.children = goals.len();
            Some(
                goals
                    .into_iter()
                    .map(|g| Env::new(g, self.depth + 1, heap.heap_point()))
                    .collect(),
            )
        }
    }

    // ── clause-based resolution ─────────────────────────────────────────

    fn try_clause<H: HypothesisTrait>(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut H,
        predicate_table: &'a PredicateTable,
        allow_new_clause: bool,
        debug: bool,
    ) -> Option<Vec<Env<'a>>> {
        let mut choices_tried = 0;

        // We need mutable access to strategy fields while also reading self.goal
        // and self.depth, so we destructure carefully inside the loop.
        'choices: loop {
            let Strategy::Clause {
                choices,
                new_clause: _,
                invent_pred: _,
            } = &mut self.strategy
            else {
                unreachable!()
            };

            let Some(clause) = choices.next() else {
                break;
            };

            if debug {
                eprintln!("[CALL] {}", clause.to_string(heap));
            }

            choices_tried += 1;
            let head = clause.head();

            if clause.meta() && !allow_new_clause {
                continue;
            }

            let Some(mut substitution) = unify(heap, head, self.goal, clause.max_arg_id) else {
                continue;
            };

            if !constraints_hold(heap, hypothesis, &substitution) {
                continue 'choices;
            }

            pre_pass_constraint(&mut substitution.arg_regs, clause.constrained_vars(), heap);

            if debug {
                let Strategy::Clause { choices, .. } = &self.strategy else {
                    unreachable!()
                };
                eprintln!(
                    "[MATCH|{}] {} / {}, choices_remaining={}",
                    self.depth,
                    heap.term_string(self.goal),
                    clause.to_string(heap),
                    choices.remaining()
                );
            }

            let new_goals = build_goals(heap, &mut substitution, clause);

            // Build the hypothesis clause if this is a meta clause -- but
            // hold it rather than pushing it, so the invented predicate
            // below is decided first.
            let pending_clause = clause.meta_data.map(|meta_data| {
                // Boxed so the common non-meta case leaves one pointer in
                // this frame rather than a ~150-byte tuple.
                let new_clause_literals: Vec<usize> = clause
                    .iter()
                    .map(|literal| {
                        build(heap, &mut substitution, clause.meta_threshold(), *literal)
                    })
                    .collect();

                let mut constraints = Vec::with_capacity(16);
                for i in 0..MAX_ARG {
                    if clause.constrained_var(i) {
                        let Some(VarId(var_id)) = substitution.get_arg(i) else {
                            unreachable!("All constrained args should have a var id");
                        };
                        constraints.push(var_id);
                    }
                }

                // A meta clause always comes from the table: test clauses
                // are built hypothesis clauses, which are never meta.
                let clause_idx = predicate_table
                    .index_of(clause)
                    .expect("a meta clause being instantiated is in the predicate table");

                Box::new((
                    Clause::new(new_clause_literals, None, clause.max_arg_id),
                    constraints,
                    meta_data,
                    clause_idx,
                ))
            });

            // Which predicate variable, if any, this try invents.
            //
            // A meta clause with a variable head resolving a variable goal has
            // just unified the two predicate variables, so the goal's predicate
            // variable now names the head of the clause about to be added. That
            // variable is the invented predicate; it is left unbound rather than
            // given a fresh constant symbol, and recorded on the hypothesis so
            // that later goals on it are denied the background facts.
            //
            // Decided here, while `clause` is still live, and registered below
            // once it is not. Registering after the `build` calls above rather
            // than before is behaviour-neutral: `build` reads the heap and the
            // substitution, never the invented-predicate registry, which is
            // consulted by `get_choices` for *later* goals.
            let invent = (clause.meta_data.is_some()
                && heap.symbol_arity(head).0 == 0
                && heap.symbol_arity(self.goal).0 == 0)
                .then(|| heap.pred_var(self.goal))
                .flatten();

            // If the invented predicate is already recorded, this clause is
            // extending an existing one rather than creating a new one, so
            // there is nothing for undo_try to remove.
            if let Some(var_id) = invent {
                if hypothesis.add_invented_pred(heap, var_id) {
                    if let Strategy::Clause { invent_pred, .. } = &mut self.strategy {
                        *invent_pred = Some(var_id);
                    }
                    if debug {
                        eprintln!(
                            "[INVENT_PRED|{}] var={} goal={}",
                            self.depth,
                            var_id,
                            heap.term_string(self.goal)
                        );
                    }
                }
            }

            if let Some(pending) = pending_clause {
                let (new_clause, constraints, meta_data, clause_idx) = *pending;
                if let Strategy::Clause { new_clause, .. } = &mut self.strategy {
                    *new_clause = true;
                }
                if debug {
                    eprintln!(
                        "[ADD_CLAUSE|{}] {} / {}",
                        self.depth,
                        heap.term_string(self.goal),
                        new_clause.to_string(heap)
                    );
                }
                hypothesis.push_clause(
                    new_clause,
                    SmallVec::from_vec(constraints),
                    &substitution.arg_regs,
                    meta_data,
                    clause_idx,
                );
                if debug {
                    eprintln!("[HYPOTHESIS]:\n{}", hypothesis.to_string(heap));
                }
            }

            return Some(self.commit(heap, substitution, new_goals, debug));
        }

        // Every program clause is spent; the hypothesis is tried last.
        if let Some(children) = self.try_hypothesis(heap, hypothesis, predicate_table, debug) {
            return Some(children);
        }

        if debug {
            eprintln!(
                "[NO_MATCH|{}] goal={} tried {} choices",
                self.depth,
                heap.term_string(self.goal),
                choices_tried,
            );
        }
        None
    }

    /// Try the hypothesis clauses this goal has left.
    ///
    /// A clause is resolved through its template -- for a `MetaSub`, the
    /// meta clause it instantiates, unified with the goal after its meta
    /// variables' registers are loaded with the recorded bindings, which is
    /// the same as unifying the clause those bindings stand for.
    ///
    /// The template's constraints are not applied and no clause is added:
    /// both happened when the clause was learned.
    fn try_hypothesis<H: HypothesisTrait>(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &H,
        predicate_table: &'a PredicateTable,
        debug: bool,
    ) -> Option<Vec<Env<'a>>> {
        loop {
            let Strategy::Clause { choices, .. } = &mut self.strategy else {
                unreachable!()
            };
            let index = choices.next_hypothesis()?;
            let protect = choices.protects_hypothesis();
            debug_assert!(
                index < hypothesis.len(),
                "the hypothesis shrank below this goal's cursor: index {index} of {}. \
                 Resuming a goal is supposed to restore the hypothesis to the length \
                 it had when the goal gathered its choices.",
                hypothesis.len()
            );

            let template = hypothesis.template(index, predicate_table);
            if debug {
                eprintln!("[CALL|H{index}] {}", template.to_string(heap));
            }

            let mut substitution = Substitution::new(template.max_arg_id);
            if let Some(threshold) = template.meta_threshold() {
                // Loaded as recorded: a variable may have been bound since,
                // so readers of these registers dereference.
                let meta_regs = &mut substitution.arg_regs[threshold..template.max_arg_id];
                hypothesis.load_subs(index, meta_regs);
            }

            let head = template.head();
            if protect && head_is_invented(heap, hypothesis, &substitution, head) {
                continue;
            }

            let Some(mut substitution) = unify_from(heap, substitution, head, self.goal) else {
                continue;
            };

            if !constraints_hold(heap, hypothesis, &substitution) {
                continue;
            }

            if debug {
                eprintln!(
                    "[MATCH|H{index}|{}] {} / {}",
                    self.depth,
                    heap.term_string(self.goal),
                    template.to_string(heap),
                );
            }

            let new_goals = build_goals(heap, &mut substitution, template);
            return Some(self.commit(heap, substitution, new_goals, debug));
        }
    }

    /// Keep a successful try's bindings and open a child for each new goal.
    fn commit(
        &mut self,
        heap: &QueryHeap,
        substitution: Substitution,
        new_goals: Vec<usize>,
        debug: bool,
    ) -> Vec<Env<'a>> {
        self.bound_vars = substitution.bound_vars;
        self.children = new_goals.len();
        if debug {
            eprintln!("Bindings: {:?}", self.bound_vars);
        }
        new_goals
            .into_iter()
            .map(|goal| Env::new(goal, self.depth + 1, heap.heap_point()))
            .collect()
    }

    fn try_conj(&mut self, heap: &QueryHeap) -> Option<Vec<Env<'a>>> {
        let Strategy::Conjunction { goals, expanded } = &mut self.strategy else {
            unreachable!()
        };
        if *expanded {
            None
        } else {
            *expanded = true;
            self.children = goals.len();
            Some(
                goals
                    .iter()
                    .map(|goal| Env::new(*goal, self.depth + 1, heap.heap_point()))
                    .collect(),
            )
        }
    }
}

/// Whether the hypothesis' constraints hold under a unification; if not,
/// its bindings are undone.
fn constraints_hold<H: HypothesisTrait>(
    heap: &mut QueryHeap,
    hypothesis: &H,
    substitution: &Substitution,
) -> bool {
    for constraints in hypothesis.constraints() {
        if !heap.check_constraints(constraints) {
            // Borrowed; see `undo_substitution`.
            heap.unbind(&substitution.bound_vars);
            return false;
        }
    }
    true
}

/// Build a goal for each body literal of a unified clause.
fn build_goals(
    heap: &mut QueryHeap,
    substitution: &mut Substitution,
    clause: &Clause,
) -> Vec<usize> {
    re_build_bound_arg_terms(heap, substitution);
    clause
        .body()
        .iter()
        .map(|&body_literal| build(heap, substitution, None, body_literal))
        .collect()
}

/// Whether the clause a loaded meta clause stands for is headed by an
/// invented predicate: its head functor is a meta variable whose register
/// holds a variable that is still unbound and names one.
///
/// `head` is the template's head and `substitution` holds the hypothesis
/// clause's bindings as recorded, so the register is dereferenced here.
fn head_is_invented<H: HypothesisTrait>(
    heap: &QueryHeap,
    hypothesis: &H,
    substitution: &Substitution,
    head: usize,
) -> bool {
    if heap[head].0 != Tag::Comp {
        return false;
    }
    match heap[head + 1] {
        (Tag::Arg, arg_id) => matches!(
            substitution.get_arg(arg_id),
            Some(VarId(var_id)) if matches!(
                heap.var_deref(var_id),
                VarId(rep) if hypothesis.is_invented_pred(heap, rep)
            )
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::head_is_invented;
    use crate::{
        heap::{
            test_prog, Heap, QueryHeap,
            Tag::{Arg, Comp, Con},
            VarBind::{Addr, VarId},
            VarReg,
        },
        program::Hypothesis,
        resolution::Substitution,
    };

    /// A template head `P(X)` with `P` at arg 1, and two query variables.
    fn template_head(heap: &mut QueryHeap) -> usize {
        heap.cells = vec![(Comp, 2), (Arg, 1), (Arg, 0)];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        0
    }

    #[test]
    fn a_head_bound_to_an_invented_predicate_variable_is_invented() {
        let mut heap = QueryHeap::new(test_prog(), None);
        let head = template_head(&mut heap);
        let mut hypothesis = Hypothesis::new();
        hypothesis.add_invented_pred(&heap, 0);

        let mut substitution = Substitution::new(2);
        substitution.set_arg(1, VarId(0));
        assert!(head_is_invented(&heap, &hypothesis, &substitution, head));

        // Another variable, not invented.
        substitution.set_arg(1, VarId(1));
        assert!(!head_is_invented(&heap, &hypothesis, &substitution, head));
    }

    #[test]
    fn a_head_register_recorded_before_its_variable_was_bound_is_dereferenced() {
        let mut heap = QueryHeap::new(test_prog(), None);
        let head = template_head(&mut heap);
        let mut hypothesis = Hypothesis::new();
        hypothesis.add_invented_pred(&heap, 0);
        let mut substitution = Substitution::new(2);
        substitution.set_arg(1, VarId(1));

        // Variable 1 now stands for the invented predicate.
        heap.var_regs[1] = VarId(0).into();
        assert!(head_is_invented(&heap, &hypothesis, &substitution, head));

        // Bound to a constant since, the predicate is no longer invented.
        let p = heap.symbols().set_const("env_tests_p");
        let p_addr = heap.heap_push((Con, p));
        heap.var_regs[0] = Addr(p_addr).into();
        assert!(!head_is_invented(&heap, &hypothesis, &substitution, head));
    }

    #[test]
    fn a_head_bound_to_a_constant_is_not_invented() {
        let mut heap = QueryHeap::new(test_prog(), None);
        let head = template_head(&mut heap);
        let p = heap.symbols().set_const("env_tests_p");
        let p_addr = heap.heap_push((Con, p));
        let mut hypothesis = Hypothesis::new();
        hypothesis.add_invented_pred(&heap, 0);

        let mut substitution = Substitution::new(2);
        substitution.set_arg(1, Addr(p_addr));
        assert!(!head_is_invented(&heap, &hypothesis, &substitution, head));
    }

    #[test]
    fn a_constant_headed_template_is_not_invented() {
        let mut heap = QueryHeap::new(test_prog(), None);
        let p = heap.symbols().set_const("env_tests_p");
        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let mut hypothesis = Hypothesis::new();
        hypothesis.add_invented_pred(&heap, 0);

        let mut substitution = Substitution::new(2);
        substitution.set_arg(1, VarId(0));
        assert!(!head_is_invented(&heap, &hypothesis, &substitution, 0));
    }
}
