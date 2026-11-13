//! Proof search via SLD resolution with backtracking and predicate invention.

use super::env::Env;
use crate::{
    heap::{Heap, QueryHeap},
    program::{Hypothesis, HypothesisTrait, PredicateTable},
    Config,
};

/// The proof search engine.
///
/// Maintains a goal stack and iteratively resolves goals against the predicate
/// table and its hypothesis. Call [`Proof::prove`] repeatedly to enumerate
/// solutions via backtracking.
///
/// `H` is the form the hypothesis is held in, which also decides whether
/// the proof learns: an owned [`Hypothesis`] may be extended, while a
/// borrowed one, or a borrowed list of ground clauses, is only tested.
#[allow(private_bounds)]
pub struct Proof<'a, H: HypothesisTrait = Hypothesis> {
    stack: Vec<Env<'a>>,
    pointer: usize,
    pub hypothesis: H,
}

impl<'a> Proof<'a> {
    /// A learning proof starting from an empty hypothesis.
    pub fn new(heap: &QueryHeap, goals: &[usize]) -> Self {
        Self::with_hypothesis(heap, goals, Hypothesis::new())
    }
}

#[allow(private_bounds)]
impl<'a, H: HypothesisTrait> Proof<'a, H> {
    /// A proof over `hypothesis`. Passing a [`Hypothesis`] by value lets
    /// the proof extend it; `&Hypothesis`, `&[&[usize]]` (packed
    /// `MetaSub`s) and `&[Clause]` are tested without learning.
    pub fn with_hypothesis(heap: &QueryHeap, goals: &[usize], hypothesis: H) -> Self {
        let stack = goals
            .iter()
            .map(|goal| Env::new(*goal, 0, heap.heap_point()))
            .collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
        }
    }

    /// `predicate_table` is borrowed for the proof's whole life, not just
    /// this call: a goal's [`Choices`](super::choices::Choices) point into
    /// the table's clause arena rather than copying out of it, and those
    /// cursors live on the goal stack until the goal is exhausted.
    pub fn prove(
        &mut self,
        heap: &mut QueryHeap,
        predicate_table: &'a PredicateTable,
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
                eprintln!("{}", self.hypothesis.to_string(heap, predicate_table));
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
                    predicate_table,
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
            env.bound_vars.clear();
        }
    }
}

#[cfg(test)]
mod learning_switch_tests {
    use super::Proof;
    use crate::{app::App, heap::QueryHeap, parser::_build_clause, program::Hypothesis};

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
        // Borrowed, so read only.
        let empty = Hypothesis::new();
        let mut testing = Proof::with_hypothesis(&heap, &[goal], &empty);
        assert!(
            !testing.prove(&mut heap, &app.predicate_table, app.config),
            "with learning off there is no clause for t/1, so the goal must fail -- \
             this is what the six test-proof call sites rely on"
        );
        assert_eq!(testing.hypothesis.len(), 0);
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

/// A hypothesis clause is resolved from its `MetaSub` against the meta
/// clause it instantiates, not from the clause that was built for it.
#[cfg(test)]
mod hypothesis_resolution_tests {
    use super::Proof;
    use crate::{
        app::App,
        heap::QueryHeap,
        heap::{Heap, VarBind::VarId},
        parser::_build_clause,
        program::{Clause, Hypothesis, MetaSubTrait, PackedMetaSubs, PredicateTable},
    };

    /// `t/1` has no clauses, so a goal on it is provable only by learning
    /// one from `P(X):-Q(X)` or by a clause already in the hypothesis.
    fn app(max_clause: usize) -> App {
        let mut app = App::default()
            .load_code("q(a). q(b). r(c). P(X):- Q(X), {P,Q}.")
            .expect("test program should load")
            .add_body_predicates(["q/1", "r/1"])
            .expect("body predicates should load");
        app.config.max_clause = max_clause;
        app
    }

    fn goal(app: &mut App, src: &str) -> usize {
        _build_clause(&mut app.prog_heap, src)[0]
    }

    /// The hypothesis's clauses, built onto `heap`.
    fn built(
        hypothesis: &Hypothesis,
        heap: &mut QueryHeap,
        predicate_table: &PredicateTable,
    ) -> Vec<Clause> {
        hypothesis
            .meta_subs
            .iter()
            .map(|meta_sub| {
                // `build_clause` wants every predicate bound to a term.
                let mut meta_sub = meta_sub.clone();
                for sub in &mut meta_sub.subs {
                    if let Some(VarId(var_id)) = sub.get_bind() {
                        *sub = heap.var_deref(var_id).into();
                    }
                }
                meta_sub.build_clause(heap, predicate_table)
            })
            .collect()
    }

    #[test]
    fn a_learned_clause_resolves_a_later_goal() {
        // One clause allowed, so `t(b)` cannot learn its own and has to be
        // proved by the `t(X):-q(X)` learned for `t(a)`.
        let mut app = app(1);
        let goals = [goal(&mut app, "t(a)."), goal(&mut app, "t(b).")];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut proof = Proof::new(&heap, &goals);

        assert!(proof.prove(&mut heap, &app.predicate_table, app.config));
        assert_eq!(proof.hypothesis.len(), 1);
    }

    #[test]
    fn a_learned_clause_does_not_resolve_a_goal_it_does_not_cover() {
        // `t(c)` needs `t(X):-r(X)`, a second clause; `t(X):-q(X)` must not
        // match it.
        let mut app = app(1);
        let goals = [goal(&mut app, "t(a)."), goal(&mut app, "t(c).")];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut proof = Proof::new(&heap, &goals);

        assert!(!proof.prove(&mut heap, &app.predicate_table, app.config));
    }

    #[test]
    fn backtracking_past_a_hypothesis_match_tries_the_next_clause() {
        // Two clauses allowed. The proof first learns `t(X):-q(X)`, which
        // matches the head of `t(c)` but fails in its body, so the search
        // must go on to learn `t(X):-r(X)`.
        let mut app = app(2);
        let goals = [goal(&mut app, "t(a)."), goal(&mut app, "t(c).")];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut proof = Proof::new(&heap, &goals);

        assert!(proof.prove(&mut heap, &app.predicate_table, app.config));
        assert_eq!(proof.hypothesis.len(), 2);
    }

    #[test]
    fn a_meta_sub_resolves_as_the_clause_built_from_it_does() {
        let mut app = app(1);
        let learn = goal(&mut app, "t(a).");
        let cases = [
            (goal(&mut app, "t(b)."), true),
            (goal(&mut app, "t(c)."), false),
            (goal(&mut app, "u(a)."), false),
        ];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut learning = Proof::new(&heap, &[learn]);
        assert!(learning.prove(&mut heap, &app.predicate_table, app.config));
        let hypothesis = learning.hypothesis.clone();
        let clauses = built(&hypothesis, &mut heap, &app.predicate_table);

        for (goal, expected) in cases {
            let mut by_meta_sub = Proof::with_hypothesis(&heap, &[goal], &hypothesis);
            let from_meta_sub = by_meta_sub.prove(&mut heap, &app.predicate_table, app.config);
            by_meta_sub.undo_all(&mut heap);

            let mut by_clause = Proof::with_hypothesis(&heap, &[goal], clauses.as_slice());
            let from_clause = by_clause.prove(&mut heap, &app.predicate_table, app.config);
            by_clause.undo_all(&mut heap);

            assert_eq!(from_meta_sub, expected);
            assert_eq!(from_clause, expected);
        }
    }

    #[test]
    fn a_hypothesis_prints_the_clause_built_from_it_and_restores_the_heap() {
        let mut app = app(1);
        let learn = goal(&mut app, "t(a).");

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut proof = Proof::new(&heap, &[learn]);
        assert!(proof.prove(&mut heap, &app.predicate_table, app.config));

        let before = (heap.cells.clone(), heap.var_regs.clone());
        let printed = proof.hypothesis.to_string(&mut heap, &app.predicate_table);
        assert_eq!(before, (heap.cells.clone(), heap.var_regs.clone()));

        let built = built(&proof.hypothesis, &mut heap, &app.predicate_table);
        assert_eq!(printed, built[0].to_string(&heap));
        assert!(
            printed.contains("t(") && printed.contains("q("),
            "{printed}"
        );
    }

    #[test]
    fn test_meta_subs_resolve_as_the_hypothesis_they_were_packed_from() {
        let mut app = app(1);
        let learn = goal(&mut app, "t(a).");
        let cases = [
            (goal(&mut app, "t(b)."), true),
            (goal(&mut app, "t(c)."), false),
            (goal(&mut app, "u(a)."), false),
        ];

        let mut heap = QueryHeap::new(&app.prog_heap, None);
        let mut learning = Proof::new(&heap, &[learn]);
        assert!(learning.prove(&mut heap, &app.predicate_table, app.config));

        let mut packed = PackedMetaSubs::default();
        packed.push(learning.hypothesis.meta_subs.iter());
        let group = packed.get(0);
        let meta_subs: Vec<&[usize]> = group.iter().collect();
        assert_eq!(meta_subs.len(), 1);

        for (goal, expected) in cases {
            let mut proof = Proof::with_hypothesis(&heap, &[goal], meta_subs.as_slice());
            assert_eq!(
                proof.prove(&mut heap, &app.predicate_table, app.config),
                expected
            );
            proof.undo_all(&mut heap);
        }

        // Without them the goal has nothing to resolve against.
        let none: &[&[usize]] = &[];
        let mut bare = Proof::with_hypothesis(&heap, &[cases[0].0], none);
        assert!(!bare.prove(&mut heap, &app.predicate_table, app.config));
    }
}
