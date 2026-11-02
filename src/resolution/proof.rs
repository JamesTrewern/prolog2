//! Proof search via SLD resolution with backtracking and predicate invention.

use super::env::Env;
use crate::{
    heap::{Heap, QueryHeap},
    program::{Clause, Hypothesis, PredicateTable},
    Config,
};

/// The proof search engine.
///
/// Maintains a goal stack and iteratively resolves goals against the predicate
/// table and the current hypothesis. Call [`Proof::prove`] repeatedly to
/// enumerate solutions via backtracking.
pub struct Proof<'a> {
    stack: Vec<Env>,
    pointer: usize,
    pub hypothesis: Hypothesis,
    test_clauses: Option<&'a [Clause]>,
    learning: bool,
}

impl<'a> Proof<'a> {
    pub fn new(heap: &QueryHeap, goals: &[usize]) -> Self {
        Self::build(heap, goals, Hypothesis::new(), true)
    }

    /// A proof that may not extend the hypothesis; see [`Proof::learning`].
    pub fn without_learning(heap: &QueryHeap, goals: &[usize]) -> Self {
        Self::build(heap, goals, Hypothesis::new(), false)
    }

    /// Create a new proof with an existing hypothesis (for negation-as-failure checks)
    pub fn with_hypothesis(heap: &QueryHeap, goals: &[usize], hypothesis: &Hypothesis) -> Self {
        Self::build(heap, goals, hypothesis.clone(), true)
    }

    /// As [`Self::with_hypothesis`], but the inherited hypothesis may not be
    /// extended.
    /// Used ub negation-as-failure and specialisation
    pub fn with_hypothesis_without_learning(
        heap: &QueryHeap,
        goals: &[usize],
        hypothesis: &Hypothesis,
    ) -> Self {
        Self::build(heap, goals, hypothesis.clone(), false)
    }

    fn build(heap: &QueryHeap, goals: &[usize], hypothesis: Hypothesis, learning: bool) -> Self {
        let stack = goals
            .iter()
            .map(|goal| Env::new(*goal, 0, heap.heap_point()))
            .collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            test_clauses: None,
            learning,
        }
    }

    /// Add clauses to be included in choices
    pub fn add_test_clauses(&mut self, clauses: &'a [Clause]) {
        self.test_clauses = Some(clauses);
    }

    pub fn prove(
        &mut self,
        heap: &mut QueryHeap,
        predicate_table: &PredicateTable,
        config: Config,
    ) -> bool {
        // Handle restart after previous success
        if self.pointer == self.stack.len() {
            if config.debug {
                eprintln!(
                    "[RESTART] pointer={} stack_len={} h_clauses={}",
                    self.pointer,
                    self.stack.len(),
                    self.hypothesis.len()
                );
                eprintln!("[RESTART_HYPOTHESIS]");
                for (i, c) in self.hypothesis.iter().enumerate() {
                    eprintln!("  [{}]: {}", i, c.to_string(heap));
                }
            }

            self.pointer -= 1;
            self.stack[self.pointer].undo_try(&mut self.hypothesis, heap, config.debug);
        }

        while self.pointer < self.stack.len() {
            if self.stack[self.pointer].got_choices {
                if config.debug {
                    eprintln!(
                        "[RETRY] {} @{}",
                        heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            } else {
                self.stack[self.pointer].get_choices(
                    heap,
                    &mut self.hypothesis,
                    &predicate_table,
                    self.test_clauses,
                    config.protect_h_preds,
                );
                if config.debug {
                    eprintln!(
                        "[TRY] {} @{}",
                        heap.term_string(self.stack[self.pointer].goal),
                        self.stack[self.pointer].goal
                    );
                }
            }
            match self.stack[self.pointer].try_choices(
                heap,
                &mut self.hypothesis,
                predicate_table,
                config,
                self.learning,
            ) {
                Some(new_goals) => {
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
                    let children =
                        self.stack[self.pointer].undo_try(&mut self.hypothesis, heap, config.debug);
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
        for env in self.stack.iter_mut() {
            heap.unbind(&env.bound_vars);
            env.bound_vars = Box::new([]);
        }
    }
}

#[cfg(test)]
mod learning_switch_tests {
    use super::Proof;
    use crate::{app::App, heap::QueryHeap, parser::_build_clause};

    /// A goal that is only provable by learning: `t(a)` has no clause, but
    /// the meta rule `P(X):-Q(X)` can invent one over the fact `q(a)`.
    fn app() -> App {
        App::default()
            .load_code("q(a). P(X):- Q(X), {P,Q}.")
            .expect("test program should load")
            .add_body_predicates(["q/1"])
            .expect("body predicate should load")
    }

    #[test]
    fn a_learning_proof_invents_a_clause_and_a_non_learning_one_does_not() {
        let mut app = app();
        let goal = _build_clause(&mut app.prog_heap, "t(a).")[0];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut learning = Proof::new(&heap, &[goal]);
        assert!(
            learning.prove(&mut heap, &app.predicate_table, app.config),
            "t(a) should be provable by inventing t(X):-q(X)"
        );
        assert_eq!(
            learning.hypothesis.len(),
            1,
            "the proof should have added exactly the one clause it needed"
        );

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut testing = Proof::without_learning(&heap, &[goal]);
        assert!(
            !testing.prove(&mut heap, &app.predicate_table, app.config),
            "with learning off there is no clause for t/1, so the goal must fail -- \
             this is what the six test-proof call sites rely on"
        );
        assert!(testing.hypothesis.is_empty());
    }

    /// The switch is on the proof, not the config: `max_clause` still has
    /// room, and it is only `learning` that makes the difference above.
    #[test]
    fn max_clause_is_not_what_disables_learning() {
        let app = app();
        assert!(
            app.config.max_clause > 0,
            "the fixture must leave room to learn, or the test above proves nothing"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::app::App;

    fn app_with(code: &str) -> App {
        App::default()
            .load_code(code)
            .expect("test program should load")
            .auto(true)
    }

    /// A tuple goal is a conjunction. This used to reach a `todo!()` in
    /// `Env::get_tup_goals` and panic, and tuples are ordinary parser output,
    /// so any query containing one brought the engine down.
    #[test]
    fn tuple_goal_proves_each_element() {
        let app = app_with("a. b.");

        assert_eq!(
            app.query_session("(a,b).")
                .expect("query should parse")
                .count(),
            1,
            "both elements hold, so the conjunction has one solution"
        );
        assert_eq!(
            app.query_session("(a,c).")
                .expect("query should parse")
                .count(),
            0,
            "c is not provable, so the conjunction fails"
        );
    }

    /// Nested tuples are left on the heap rather than flattened, so the inner
    /// one becomes a conjunction of its own when the search reaches it.
    #[test]
    fn nested_tuple_goal_proves_each_element() {
        let app = app_with("a. b. c.");

        assert_eq!(
            app.query_session("(a,(b,c)).")
                .expect("query should parse")
                .count(),
            1
        );
        assert_eq!(
            app.query_session("(a,(b,d)).")
                .expect("query should parse")
                .count(),
            0
        );
    }

    /// A tuple goal binds variables like any other conjunction, and the
    /// bindings have to agree across the elements.
    #[test]
    fn tuple_goal_shares_bindings_between_elements() {
        let app = app_with("p(1). p(2). q(2). q(3).");

        let solutions: Vec<String> = app
            .query_session("(p(X),q(X)).")
            .expect("query should parse")
            .map(|solution| format!("{:?}", solution))
            .collect();

        assert_eq!(
            solutions.len(),
            1,
            "only X=2 satisfies both sides, got {solutions:?}"
        );
        assert!(
            solutions[0].contains('2'),
            "expected X=2, got {solutions:?}"
        );
    }
}
