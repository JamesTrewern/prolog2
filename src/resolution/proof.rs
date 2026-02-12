use std::sync::Arc;

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

pub type Binding = (usize, usize);
#[derive(Debug)]
pub(super) struct Env {
    pub(super) goal: usize,
    pub(super) bindings: Box<[Binding]>,
    pub(super) choices: Vec<Clause>,
    pred_function: Option<PredicateFunction>,
    pred_function_tried: bool,
    pub(crate) got_choices: bool,
    pub(super) new_clause: bool,
    pub(super) invent_pred: bool,
    pub(super) children: usize,
    pub(super) depth: usize,
    total_choice_count: usize,
    heap_point: usize, //How big was the heap after this goal was created
}

impl Env {
    pub fn new(goal: usize, depth: usize, heap_point: usize) -> Self {
        Env {
            goal,
            bindings: Box::new([]),
            choices: Vec::new(),
            pred_function: None,
            pred_function_tried: false,
            got_choices: false,
            new_clause: false,
            invent_pred: false,
            children: 0,
            depth,
            total_choice_count: 0,
            heap_point,
        }
    }

    pub fn get_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        predicate_table: &PredicateTable,
    ) {
        self.got_choices = true;
        self.heap_point = heap.heap_len();
        let (symbol, arity) = heap.str_symbol_arity(self.goal);

        self.choices = hypothesis.iter().map(|clause| clause.clone()).collect();

        if symbol == 0 {
            // Add meta-rules (variable clauses) FIRST so they're at the start
            if let Some(clauses) = predicate_table.get_variable_clauses(arity) {
                self.choices.extend(clauses.iter().map(|c| c.clone()));
            }
            // Add body predicates LAST so they're at the end and get popped first
            // This ensures we try grounded predicates before inventing new ones
            self.choices.extend(
                predicate_table
                    .get_body_clauses(arity)
                    .into_iter()
                    .map(|c| c),
            );
            self.total_choice_count = self.choices.len();
        } else {
            match predicate_table.get_predicate((symbol, arity)) {
                Some(Predicate::Function(pred_function)) => {
                    self.pred_function = Some(pred_function)
                }
                Some(Predicate::Clauses(clauses)) => {
                    self.choices.extend(clauses.iter().map(|c| c.clone()));
                    self.total_choice_count = self.choices.len();
                }
                None => {
                    if let Some(clauses) = predicate_table.get_variable_clauses(arity) {
                        self.choices.extend(clauses.iter().map(|c| c.clone()));
                        self.total_choice_count = self.choices.len();
                    }
                }
            }
        };
    }

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
        if self.new_clause {
            let clause = hypothesis.pop_clause();
            if debug {
                eprintln!(
                    "[UNDO_CLAUSE] depth={} clause={}",
                    self.depth,
                    clause.to_string(heap)
                );
            }
            *h_clauses -= 1;
            self.new_clause = false;
            if self.invent_pred {
                *invented_preds -= 1;
                self.invent_pred = false;
            }
        }
        heap.unbind(&self.bindings);
        heap.truncate(self.heap_point);
        self.children
    }

    pub fn try_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        allow_new_clause: bool,
        allow_new_pred: bool,
        predicate_table: Arc<PredicateTable>,
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

        if let Some(pred_function) = self.pred_function {
            if !self.pred_function_tried {
                self.pred_function_tried = true;
                match pred_function(heap, hypothesis, self.goal, predicate_table.clone(), config) {
                    PredReturn::True => return Some(Vec::new()),
                    PredReturn::False => {
                        // Fall through to try clause-based choices
                    }
                    PredReturn::Binding(bindings) => {
                        self.bindings = bindings.into_boxed_slice();
                        heap.bind(&self.bindings);
                        return Some(Vec::new());
                    }
                }
            }
        }

        let mut choices_tried = 0;

        'choices: while let Some(clause) = self.choices.pop() {
            if debug{
                eprintln!(
                        "[CALL] {}",
                        clause.to_string(heap)
                    );
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
                    eprintln!(
                        "[MATCH] depth={} goal={} clause={}, choices_remaining={}",
                        self.depth,
                        heap.term_string(self.goal),
                        clause.to_string(heap),
                        self.choices.len()
                    );
                }

                re_build_bound_arg_terms(heap, &mut substitution);

                // Check if we need to invent a predicate BEFORE building goals
                let mut invented_pred_addr: Option<usize> = None;
                if clause.meta() {
                    if heap.str_symbol_arity(head).0 == 0 && heap.str_symbol_arity(self.goal).0 == 0
                    {
                        self.invent_pred = true;
                        let pred_symbol = SymbolDB::set_const(format!("pred_{}", hypothesis.len()));
                        let pred_addr = heap.set_const(pred_symbol);
                        substitution.set_arg(0, pred_addr);

                        substitution =
                            substitution.push((heap.deref_addr(self.goal + 1), pred_addr, true));
                        invented_pred_addr = Some(pred_addr);
                    }
                }

                // Build new goals (now with invented predicate if applicable)
                let new_goals: Vec<usize> = clause
                    .body()
                    .iter()
                    .map(|&body_literal| build(heap, &mut substitution, None, body_literal))
                    .collect();

                // Build hypothesis clause if meta
                if clause.meta() {
                    self.new_clause = true;

                    let new_clause_literals: Vec<usize> = clause
                        .iter()
                        .map(|literal| build(heap, &mut substitution, clause.meta_vars, *literal))
                        .collect();

                    let mut constraints = Vec::with_capacity(16);
                    for i in 0..32 {
                        if unsafe { clause.meta_var(i).unwrap_unchecked() } {
                            constraints.push(unsafe { substitution.get_arg(i).unwrap_unchecked() });
                        }
                    }

                    let new_clause = Clause::new(new_clause_literals, None);
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
                    hypothesis.push_clause(new_clause, constraints.into());
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
            eprintln!(
                "[NO_MATCH] depth={} goal={} tried {} choices, Originally had {} choices",
                self.depth,
                heap.term_string(self.goal),
                choices_tried,
                self.total_choice_count
            );
        }
        None
    }
}

pub struct Proof {
    stack: Vec<Env>,
    pointer: usize,
    pub hypothesis: Hypothesis,
    pub heap: QueryHeap,
    h_clauses: usize,
    invented_preds: usize,
}

impl Proof {
    pub fn new(heap: QueryHeap, goals: &[usize]) -> Self {
        let hypothesis = Hypothesis::new();
        let stack = goals.iter().map(|goal| Env::new(*goal, 0, heap.heap_len())).collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            heap,
            h_clauses: 0,
            invented_preds: 0,
        }
    }

    /// Create a new proof with an existing hypothesis (for negation-as-failure checks)
    pub fn with_hypothesis(heap: QueryHeap, goals: &[usize], hypothesis: Hypothesis) -> Self {
        let h_clauses = hypothesis.len();
        let stack = goals.iter().map(|goal| Env::new(*goal, 0, heap.heap_len())).collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            heap,
            h_clauses,
            invented_preds: 0,
        }
    }

    pub fn prove(
        &mut self,
        predicate_table: Arc<PredicateTable>,
        config: Config,
    ) -> bool {
        // Handle restart after previous success
        if self.pointer == self.stack.len() {
            if config.debug {
                eprintln!(
                    "[RESTART] pointer={} stack_len={} h_clauses={}",
                    self.pointer,
                    self.stack.len(),
                    self.h_clauses
                );
                eprintln!("[RESTART_HYPOTHESIS]");
                for (i, c) in self.hypothesis.iter().enumerate() {
                    eprintln!("  [{}]: {}", i, c.to_string(&self.heap));
                }
            }

            self.pointer -= 1;
            self.stack[self.pointer].undo_try(
                &mut self.hypothesis,
                &mut self.heap,
                &mut self.h_clauses,
                &mut self.invented_preds,
                config.debug,
            );
        }

        while self.pointer < self.stack.len() {
            if self.stack[self.pointer].got_choices {
                if config.debug {
                    eprintln!(
                        "[RETRY] goal={} addr={}",
                        self.heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            } else {
                self.stack[self.pointer].get_choices(
                    &mut self.heap,
                    &mut self.hypothesis,
                    &predicate_table,
                );
                if config.debug {
                    eprintln!(
                        "[TRY] goal={} addr={}",
                        self.heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            }
            match self.stack[self.pointer].try_choices(
                &mut self.heap,
                &mut self.hypothesis,
                self.h_clauses < config.max_clause,
                self.invented_preds < config.max_pred,
                predicate_table.clone(),
                config,
                config.debug,
            ) {
                Some(new_goals) => {
                    if self.stack[self.pointer].new_clause {
                        self.h_clauses += 1;
                    }
                    if self.stack[self.pointer].invent_pred {
                        self.invented_preds += 1;
                    }
                    self.pointer += 1;
                    self.stack.splice(self.pointer..self.pointer, new_goals);
                }
                None => {
                    if self.pointer == 0 {
                        if config.debug {
                            eprintln!("[FAILED] First goal exhausted");
                        }
                        return false;
                    }
                    // Reset got_choices for the goal we're backtracking FROM
                    // This ensures if we reach this goal again via a different proof path,
                    // it will get fresh choices based on the new hypothesis state
                    self.stack[self.pointer].got_choices = false;
                    self.stack[self.pointer].choices.clear();
                    self.stack[self.pointer].pred_function_tried = false;

                    self.pointer -= 1;
                    let children = self.stack[self.pointer].undo_try(
                        &mut self.hypothesis,
                        &mut self.heap,
                        &mut self.h_clauses,
                        &mut self.invented_preds,
                        config.debug,
                    );
                    self.stack
                        .drain((self.pointer + 1)..(self.pointer + 1 + children));
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {}
