//! Goal environment for the SLD resolution proof search.
//!
//! Each [`Env`] represents a single goal on the proof stack. The [`Strategy`]
//! enum separates clause-based resolution from native predicate evaluation,
//! keeping the two execution paths explicit at the type level.

use smallvec::SmallVec;

use crate::{
    heap::{heap::Heap, query_heap::QueryHeap, symbol_db::SymbolDB},
    predicate_modules::{PredReturn, PredicateFunction},
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_table::{Predicate, PredicateTable},
    },
    resolution::{
        build::{build, re_build_bound_arg_terms},
        unification::unify,
    },
    Config,
};

/// A variable binding: `(source_addr, target_addr)` on the heap.
pub type Binding = (usize, usize);

/// How a goal is resolved: either by unifying with clauses or by calling a
/// native predicate function.
#[derive(Debug)]
pub(crate) enum Strategy {
    /// Resolution via clause unification (standard SLD + meta-interpretive learning).
    Clause {
        choices: Vec<Clause>,
        /// Whether a hypothesis clause was added on the last successful try.
        new_clause: bool,
        /// Whether a new predicate symbol was invented on the last successful try.
        invent_pred: bool,
        total_choice_count: usize,
    },
    /// Resolution via a native predicate function, with optional backtrackable
    /// alternatives produced by [`PredReturn::Choices`].
    Native {
        function: PredicateFunction,
        /// Alternative results to try on backtracking. Each entry is a
        /// `(bindings, sub_goals)` pair, popped one at a time.
        alternatives: Vec<(Vec<Binding>, Vec<usize>)>,
        /// Whether the predicate function has been called yet.
        called: bool,
    },
}

/// A goal environment in the proof search.
///
/// Shared fields live directly on the struct; the divergent clause-vs-native
/// state lives inside [`Strategy`].
#[derive(Debug)]
pub(super) struct Env {
    pub(super) goal: usize,
    pub(super) bindings: Box<[Binding]>,
    pub(super) children: usize,
    pub(super) depth: usize,
    pub(crate) got_choices: bool,
    pub(super) heap_point: usize,
    pub(super) strategy: Strategy,
}

impl Env {
    pub fn new(goal: usize, depth: usize, heap_point: usize) -> Self {
        Env {
            goal,
            bindings: Box::new([]),
            children: 0,
            depth,
            got_choices: false,
            heap_point,
            // Default to an empty clause strategy; overwritten by get_choices.
            strategy: Strategy::Clause {
                choices: Vec::new(),
                new_clause: false,
                invent_pred: false,
                total_choice_count: 0,
            },
        }
    }

    // ── accessors for strategy-specific fields ──────────────────────────

    /// Whether the last successful clause try added a hypothesis clause.
    pub fn new_clause(&self) -> bool {
        match &self.strategy {
            Strategy::Clause { new_clause, .. } => *new_clause,
            Strategy::Native { .. } => false,
        }
    }

    /// Whether the last successful clause try invented a new predicate.
    pub fn invent_pred(&self) -> bool {
        match &self.strategy {
            Strategy::Clause { invent_pred, .. } => *invent_pred,
            Strategy::Native { .. } => false,
        }
    }

    // ── choice gathering ────────────────────────────────────────────────

    pub fn get_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        predicate_table: &PredicateTable,
    ) {
        self.got_choices = true;
        self.heap_point = heap.heap_len();
        let (symbol, arity) = heap.str_symbol_arity(self.goal);

        if symbol == 0 {
            // Variable goal — gather meta-rules and body clauses.
            let mut choices = Vec::new();
            choices.extend_from_slice(hypothesis);

            if let Some(clauses) = predicate_table.get_variable_clauses(arity) {
                choices.extend_from_slice(clauses);
            }
            choices.extend(predicate_table.get_body_clauses(arity).cloned());
            let total = choices.len();
            self.strategy = Strategy::Clause {
                choices,
                new_clause: false,
                invent_pred: false,
                total_choice_count: total,
            };
        } else {
            match predicate_table.get_predicate((symbol, arity)) {
                Some(Predicate::Function(pred_function)) => {
                    self.strategy = Strategy::Native {
                        function: *pred_function,
                        alternatives: Vec::new(),
                        called: false,
                    };
                }
                Some(Predicate::Clauses(clauses)) => {
                    let mut choices = Vec::new();
                    choices.extend_from_slice(hypothesis);
                    choices.extend_from_slice(clauses);
                    let total = choices.len();
                    self.strategy = Strategy::Clause {
                        choices,
                        new_clause: false,
                        invent_pred: false,
                        total_choice_count: total,
                    };
                }
                None => {
                    let mut choices = Vec::new();
                    choices.extend_from_slice(hypothesis);
                    if let Some(clauses) = predicate_table.get_variable_clauses(arity) {
                        choices.extend_from_slice(clauses);
                    }
                    let total = choices.len();
                    self.strategy = Strategy::Clause {
                        choices,
                        new_clause: false,
                        invent_pred: false,
                        total_choice_count: total,
                    };
                }
            }
        }
    }

    // ── undo / backtrack ────────────────────────────────────────────────

    pub fn undo_try(
        &mut self,
        hypothesis: &mut Hypothesis,
        heap: &mut QueryHeap,
        h_clauses: &mut usize,
        invented_preds: &mut usize,
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
                let clause = hypothesis.pop_clause();
                if debug {
                    eprintln!(
                        "[UNDO_CLAUSE] depth={} clause={}",
                        self.depth,
                        clause.to_string(heap)
                    );
                }
                *h_clauses -= 1;
                *new_clause = false;
                if *invent_pred {
                    *invented_preds -= 1;
                    *invent_pred = false;
                }
            }
        }
        heap.unbind(&self.bindings);
        heap.truncate(self.heap_point);
        self.children
    }

    // ── reset on backtrack-from ─────────────────────────────────────────

    /// Reset this env when backtracking past it, so it gets fresh choices on
    /// a future visit via a different proof path.
    pub fn reset(&mut self) {
        self.got_choices = false;
        match &mut self.strategy {
            Strategy::Clause { choices, .. } => choices.clear(),
            Strategy::Native {
                called,
                alternatives,
                ..
            } => {
                *called = false;
                alternatives.clear();
            }
        }
    }

    // ── try choices (dispatch) ──────────────────────────────────────────

    pub fn try_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        allow_new_clause: bool,
        allow_new_pred: bool,
        predicate_table: &PredicateTable,
        config: Config,
        debug: bool,
    ) -> Option<Vec<Env>> {
        if self.depth > config.max_depth {
            if debug {
                eprintln!(
                    "[FAIL_ON_DEPTH] depth={} goal={}",
                    self.depth,
                    heap.term_string(self.goal),
                );
            }
            return None;
        }

        match &self.strategy {
            Strategy::Native { .. } => {
                self.try_native(heap, hypothesis, predicate_table, config, debug)
            }
            Strategy::Clause { .. } => self.try_clause(
                heap,
                hypothesis,
                allow_new_clause,
                allow_new_pred,
                predicate_table,
                config,
                debug,
            ),
        }
    }

    // ── native predicate resolution ─────────────────────────────────────

    fn try_native(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        predicate_table: &PredicateTable,
        config: Config,
        _debug: bool,
    ) -> Option<Vec<Env>> {
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
            match function(heap, hypothesis, self.goal, predicate_table, config) {
                PredReturn::True => return Some(Vec::new()),
                PredReturn::False => return None,
                PredReturn::Success(bindings, goals) => {
                    self.bindings = bindings.into_boxed_slice();
                    heap.bind(&self.bindings);
                    if goals.is_empty() {
                        return Some(Vec::new());
                    }
                    return Some(
                        goals
                            .into_iter()
                            .map(|g| Env::new(g, self.depth + 1, heap.heap_len()))
                            .collect(),
                    );
                }
                PredReturn::Choices(mut alts) => {
                    // Reverse so we can pop in order (first alternative last in vec).
                    alts.reverse();
                    *alternatives = alts;
                    // Fall through to pop the first alternative below.
                }
            }
        }

        // Pop the next alternative (either from initial Choices or on backtrack).
        let Strategy::Native { alternatives, .. } = &mut self.strategy else {
            unreachable!()
        };
        let (bindings, goals) = alternatives.pop()?;
        self.bindings = bindings.into_boxed_slice();
        heap.bind(&self.bindings);
        if goals.is_empty() {
            Some(Vec::new())
        } else {
            self.children = goals.len();
            Some(
                goals
                    .into_iter()
                    .map(|g| Env::new(g, self.depth + 1, heap.heap_len()))
                    .collect(),
            )
        }
    }

    // ── clause-based resolution ─────────────────────────────────────────

    fn try_clause(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        allow_new_clause: bool,
        allow_new_pred: bool,
        _predicate_table: &PredicateTable,
        _config: Config,
        debug: bool,
    ) -> Option<Vec<Env>> {
        let mut choices_tried = 0;

        // We need mutable access to strategy fields while also reading self.goal
        // and self.depth, so we destructure carefully inside the loop.
        'choices: loop {
            let Strategy::Clause {
                choices,
                new_clause: _,
                invent_pred: _,
                total_choice_count: _,
            } = &mut self.strategy
            else {
                unreachable!()
            };

            let Some(clause) = choices.pop() else {
                break;
            };

            if debug {
                eprintln!("[CALL] {}", clause.to_string(heap));
            }

            choices_tried += 1;
            let head = clause.head();

            if clause.meta() {
                if !allow_new_clause {
                    continue;
                } else if !allow_new_pred
                    && heap.str_symbol_arity(head).0 == 0
                    && heap.str_symbol_arity(self.goal).0 == 0
                {
                    continue;
                }
            }

            if let Some(mut substitution) = unify(heap, head, self.goal) {
                for constraints in &hypothesis.constraints {
                    if !substitution.check_constraints(&constraints, heap) {
                        continue 'choices;
                    }
                }

                if debug {
                    let Strategy::Clause { choices, .. } = &self.strategy else {
                        unreachable!()
                    };
                    eprintln!(
                        "[MATCH] depth={} goal={} clause={}, choices_remaining={}",
                        self.depth,
                        heap.term_string(self.goal),
                        clause.to_string(heap),
                        choices.len()
                    );
                }

                re_build_bound_arg_terms(heap, &mut substitution);

                // Check if we need to invent a predicate BEFORE building goals
                let mut invented_pred_addr: Option<usize> = None;
                if clause.meta() {
                    if heap.str_symbol_arity(head).0 == 0 && heap.str_symbol_arity(self.goal).0 == 0
                    {
                        let pred_symbol = SymbolDB::set_const(format!("pred_{}", hypothesis.len()));
                        let pred_addr = heap.set_const(pred_symbol);
                        substitution.set_arg(0, pred_addr);
                        substitution =
                            substitution.push((heap.deref_addr(self.goal + 1), pred_addr, true));
                        invented_pred_addr = Some(pred_addr);

                        if let Strategy::Clause { invent_pred, .. } = &mut self.strategy {
                            *invent_pred = true;
                        }
                    }
                }

                // Build new goals
                let new_goals: Vec<usize> = clause
                    .body()
                    .iter()
                    .map(|&body_literal| build(heap, &mut substitution, None, body_literal))
                    .collect();

                // Build hypothesis clause if meta
                if clause.meta() {
                    if let Strategy::Clause { new_clause, .. } = &mut self.strategy {
                        *new_clause = true;
                    }

                    let new_clause_literals: Vec<usize> = clause
                        .iter()
                        .map(|literal| build(heap, &mut substitution, clause.meta_vars, *literal))
                        .collect();

                    let mut constraints = Vec::with_capacity(16);
                    for i in 0..32 {
                        if clause.constrained_var(i) {
                            constraints.push(unsafe { substitution.get_arg(i).unwrap_unchecked() });
                        }
                    }

                    let new_clause = Clause::new(new_clause_literals, None, None);
                    if debug {
                        eprintln!(
                            "[ADD_CLAUSE] depth={} goal={} clause={}",
                            self.depth,
                            heap.term_string(self.goal),
                            new_clause.to_string(heap)
                        );
                        if invented_pred_addr.is_some() {
                            eprintln!(
                                "[INVENT_PRED] invented predicate for goal={}",
                                heap.term_string(self.goal)
                            );
                        }
                    }
                    hypothesis.push_clause(new_clause, SmallVec::from_vec(constraints));
                    if debug {
                        eprintln!("[HYPOTHESIS]:\n{}", hypothesis.to_string(heap));
                    }
                }

                self.bindings = substitution.get_bindings();
                self.children = new_goals.len();
                if debug {
                    eprintln!("Bindings: {:?}", self.bindings);
                }
                heap.bind(&self.bindings);

                return Some(
                    new_goals
                        .into_iter()
                        .map(|goal| Env::new(goal, self.depth + 1, heap.heap_len()))
                        .collect(),
                );
            }
        }

        if debug {
            let total = match &self.strategy {
                Strategy::Clause {
                    total_choice_count, ..
                } => *total_choice_count,
                _ => 0,
            };
            eprintln!(
                "[NO_MATCH] depth={} goal={} tried {} choices, Originally had {} choices",
                self.depth,
                heap.term_string(self.goal),
                choices_tried,
                total
            );
        }
        None
    }
}
