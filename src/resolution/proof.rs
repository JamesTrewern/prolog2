//! Proof search via SLD resolution with backtracking and predicate invention.

use crate::{
    heap::{heap::Heap, query_heap::QueryHeap},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

use super::env::Env;

/// The proof search engine.
///
/// Maintains a goal stack and iteratively resolves goals against the predicate
/// table and the current hypothesis. Call [`Proof::prove`] repeatedly to
/// enumerate solutions via backtracking.
pub struct Proof {
    stack: Vec<Env>,
    pointer: usize,
    pub hypothesis: Hypothesis,
    h_clauses: usize,
    invented_preds: usize,
}

impl Proof {
    pub fn new(heap: &QueryHeap, goals: &[usize]) -> Self {
        let hypothesis = Hypothesis::new();
        let stack = goals
            .iter()
            .map(|goal| Env::new(*goal, 0, heap.heap_len()))
            .collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            h_clauses: 0,
            invented_preds: 0,
        }
    }

    /// Create a new proof with an existing hypothesis (for negation-as-failure checks)
    pub fn with_hypothesis(heap: &QueryHeap, goals: &[usize], hypothesis: Hypothesis) -> Self {
        let h_clauses = hypothesis.len();
        let stack = goals
            .iter()
            .map(|goal| Env::new(*goal, 0, heap.heap_len()))
            .collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            h_clauses,
            invented_preds: 0,
        }
    }

    pub fn prove(&mut self, heap: &mut QueryHeap, predicate_table: &PredicateTable, config: Config) -> bool {
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
                    eprintln!("  [{}]: {}", i, c.to_string(heap));
                }
            }

            self.pointer -= 1;
            self.stack[self.pointer].undo_try(
                &mut self.hypothesis,
                heap,
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
                        heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            } else {
                self.stack[self.pointer].get_choices(
                    heap,
                    &mut self.hypothesis,
                    &predicate_table,
                );
                if config.debug {
                    eprintln!(
                        "[TRY] goal={} addr={}",
                        heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            }
            match self.stack[self.pointer].try_choices(
                heap,
                &mut self.hypothesis,
                self.h_clauses < config.max_clause,
                self.invented_preds < config.max_pred,
                predicate_table,
                config,
                config.debug,
            ) {
                Some(new_goals) => {
                    if self.stack[self.pointer].new_clause() {
                        self.h_clauses += 1;
                    }
                    if self.stack[self.pointer].invent_pred() {
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
                    // Reset this goal so it gets fresh choices on a future visit
                    self.stack[self.pointer].reset(heap);
                    self.pointer -= 1;
                    let children = self.stack[self.pointer].undo_try(
                        &mut self.hypothesis,
                        heap,
                        &mut self.h_clauses,
                        &mut self.invented_preds,
                        config.debug,
                    );
                    // The parent's `undo_try` truncated the heap to the parent's
                    // `heap_point`, which reclaims the cells the drained children
                    // allocated. That is sufficient for ordinary bindings (whose
                    // source vars live above the truncation point), but a forward
                    // binding produced by `re_build_bound_arg_terms`
                    // (old_var -> freshly_built_high_addr) has a source var BELOW
                    // the truncation point that survives the truncate. If we drop
                    // the child env without restoring that source ref, the cell is
                    // left pointing at a truncated-away target and a later deref
                    // panics. Restore any such surviving source refs here.
                    let hl = heap.heap_len();
                    for env in
                        &self.stack[(self.pointer + 1)..(self.pointer + 1 + children)]
                    {
                        for &(src, _) in env.bindings.iter() {
                            if src < hl {
                                if let (crate::heap::heap::Tag::Ref, p) = &mut heap[src] {
                                    *p = src;
                                }
                            }
                        }
                    }
                    self.stack
                        .drain((self.pointer + 1)..(self.pointer + 1 + children));
                }
            }
        }
        true
    }

    /// Undo every binding still recorded across the proof's goal stack,
    /// restoring each bound source ref to a self-reference.
    ///
    /// Used by negation-as-failure (`not/1`): the inner proof runs on the
    /// *shared* parent heap, so on success it leaves the solution's bindings
    /// (including forward bindings to low parent vars) in place. The caller
    /// must call this and then truncate the heap back to its pre-call length
    /// so the inner proof leaves no trace on the parent heap.
    pub fn undo_all(&mut self, heap: &mut QueryHeap) {
        let hl = heap.heap_len();
        for env in self.stack.iter_mut() {
            for &(src, _) in env.bindings.iter() {
                if src < hl {
                    if let (crate::heap::heap::Tag::Ref, p) = &mut heap[src] {
                        *p = src;
                    }
                }
            }
            env.bindings = Box::new([]);
        }
    }
}

#[cfg(test)]
mod tests {}
