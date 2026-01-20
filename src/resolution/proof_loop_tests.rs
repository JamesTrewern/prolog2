/// Comprehensive tests for proof loop focusing on:
/// 1. Undo/retry mechanics - ensuring environment effects are properly reversed
/// 2. Constraint checking - preventing invalid predicate symbol sharing
/// 
/// These tests assume the heap, clause, and unification modules work correctly
/// and focus on integration-level behavior of the proof stack.

#[cfg(test)]
mod proof_loop_tests {
    use std::sync::Arc;
    use crate::{
        heap::{
            heap::{Cell, Heap, Tag, EMPTY_LIS},
            query_heap::QueryHeap,
            symbol_db::SymbolDB,
        },
        program::{
            clause::{BitFlag64, Clause},
            hypothesis::Hypothesis,
            predicate_table::PredicateTable,
        },
        resolution::{
            proof::{Env, Proof},
            unification::{unify, Substitution},
            build::{build, re_build_bound_arg_terms},
        },
        Config,
    };

    // ============================================================================
    // HELPER FUNCTIONS
    // ============================================================================

    fn setup_symbols() -> (usize, usize, usize, usize, usize) {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let r = SymbolDB::set_const("r".into());
        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());
        (p, q, r, a, b)
    }

    /// Create a simple heap state snapshot for comparison
    fn snapshot_heap_refs(heap: &impl Heap, addresses: &[usize]) -> Vec<(usize, usize)> {
        addresses
            .iter()
            .map(|&addr| (heap[addr].0 as usize, heap[addr].1))
            .collect()
    }

    /// Check if a Ref cell is unbound (points to itself)
    fn is_unbound_ref(heap: &impl Heap, addr: usize) -> bool {
        matches!(heap[addr], (Tag::Ref, ptr) if ptr == addr)
    }

    // ============================================================================
    // TEST CATEGORY 1: BINDING/UNBINDING CORRECTNESS
    // ============================================================================

    /// Test that unbind correctly restores Ref cells to self-referencing state
    #[test]
    fn test_unbind_restores_self_reference() {
        let (p, _, _, a, _) = setup_symbols();
        
        let mut heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Unbound ref
            (Tag::Ref, 1),      // 1: Unbound ref  
            (Tag::Con, a),      // 2: Constant 'a'
            (Tag::Func, 2),     // 3: p/1
            (Tag::Con, p),      // 4
            (Tag::Ref, 5),      // 5: Unbound ref
        ];
        
        // Verify initial state
        assert!(is_unbound_ref(&heap, 0));
        assert!(is_unbound_ref(&heap, 1));
        assert!(is_unbound_ref(&heap, 5));
        
        // Create bindings: 0 -> 2, 1 -> 3, 5 -> 2
        let bindings: Vec<(usize, usize)> = vec![(0, 2), (1, 3), (5, 2)];
        
        // Apply bindings
        heap.bind(&bindings);
        
        // Verify bindings took effect
        assert_eq!(heap[0], (Tag::Ref, 2));
        assert_eq!(heap[1], (Tag::Ref, 3));
        assert_eq!(heap[5], (Tag::Ref, 2));
        
        // Unbind
        heap.unbind(&bindings);
        
        // Verify refs are restored to self-reference
        assert!(is_unbound_ref(&heap, 0), "Ref 0 not properly unbound");
        assert!(is_unbound_ref(&heap, 1), "Ref 1 not properly unbound");
        assert!(is_unbound_ref(&heap, 5), "Ref 5 not properly unbound");
    }

    /// Test that unbind only affects Ref cells, not other cell types
    #[test]
    fn test_unbind_only_affects_refs() {
        let (p, _, _, a, b) = setup_symbols();
        
        let mut heap: Vec<Cell> = vec![
            (Tag::Con, a),      // 0: Should NOT change
            (Tag::Ref, 1),      // 1: Should change
            (Tag::Arg, 0),      // 2: Should NOT change
            (Tag::Int, 42),     // 3: Should NOT change
        ];
        
        let bindings = vec![(0, 3), (1, 0), (2, 0), (3, 0)];
        
        // Force modify all cells to simulate a corrupted bind
        heap[0].1 = 3;
        heap[1].1 = 0;
        heap[2].1 = 0;
        heap[3].1 = 0;
        
        heap.unbind(&bindings);
        
        // Only Ref cell (index 1) should be reset
        assert_eq!(heap[0], (Tag::Con, 3), "Con cell incorrectly modified by unbind");
        assert_eq!(heap[1], (Tag::Ref, 1), "Ref cell should be self-referencing");
        assert_eq!(heap[2], (Tag::Arg, 0), "Arg cell incorrectly modified by unbind");
        assert_eq!(heap[3], (Tag::Int, 0), "Int cell incorrectly modified by unbind");
    }

    /// Test binding chains are properly handled during unbind
    #[test]
    fn test_unbind_binding_chain() {
        let mut heap: Vec<Cell> = vec![
            (Tag::Ref, 0),  // 0
            (Tag::Ref, 1),  // 1
            (Tag::Ref, 2),  // 2
            (Tag::Ref, 3),  // 3
        ];
        
        // Create chain: 0 -> 1 -> 2 -> 3
        let bindings = vec![(0, 1), (1, 2), (2, 3)];
        heap.bind(&bindings);
        
        assert_eq!(heap.deref_addr(0), 3);
        
        heap.unbind(&bindings);
        
        // All should be self-referencing again
        for i in 0..=3 {
            assert!(is_unbound_ref(&heap, i), "Ref {} not properly unbound", i);
        }
    }

    // ============================================================================
    // TEST CATEGORY 2: CONSTRAINT CHECKING
    // ============================================================================

    /// Test that check_constraints correctly identifies disallowed bindings
    #[test]
    fn test_constraints_block_same_predicate_binding() {
        let (p, q, _, a, b) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Will be bound to addr 2
            (Tag::Ref, 1),      // 1: Will be bound to addr 2 (same!)
            (Tag::Con, p),      // 2: Predicate symbol 'p'
            (Tag::Con, q),      // 3: Predicate symbol 'q'
        ];
        
        // Constraints: addresses 0 and 1 cannot be bound to the same value
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        // Create substitution where both refs point to same address
        let mut sub = Substitution::default();
        sub = sub.push((0, 2, false));
        sub = sub.push((1, 2, false));  // Both bound to address 2 (pred 'p')
        
        // This should fail the constraint check
        assert!(
            !sub.check_constraints(&constraints, &heap),
            "Constraints should block when two meta-vars bound to same predicate"
        );
    }

    /// Test that constraints allow different predicate bindings
    #[test]
    fn test_constraints_allow_different_predicates() {
        let (p, q, _, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0
            (Tag::Ref, 1),      // 1
            (Tag::Con, p),      // 2: 'p'
            (Tag::Con, q),      // 3: 'q'
        ];
        
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        // Both bound to DIFFERENT addresses
        let mut sub = Substitution::default();
        sub = sub.push((0, 2, false));  // Bound to 'p'
        sub = sub.push((1, 3, false));  // Bound to 'q'
        
        assert!(
            sub.check_constraints(&constraints, &heap),
            "Constraints should allow different predicate bindings"
        );
    }

    /// Test constraints with dereferencing chains
    #[test]
    fn test_constraints_with_deref_chain() {
        let (p, _, _, _, _) = setup_symbols();
        
        let mut heap: Vec<Cell> = vec![
            (Tag::Ref, 1),      // 0: Points to 1
            (Tag::Ref, 2),      // 1: Points to 2
            (Tag::Con, p),      // 2: 'p'
            (Tag::Ref, 4),      // 3: Points to 4
            (Tag::Ref, 2),      // 4: Points to 2 (same final target!)
        ];
        
        // Constraints on addresses that dereference to the same value
        let constraints: Arc<[usize]> = vec![0, 3].into();
        
        let mut sub = Substitution::default();
        // Both ultimately resolve to address 2 after dereferencing
        sub = sub.push((0, 1, false));
        sub = sub.push((3, 4, false));
        
        // After deref_addr, both 0 and 3 resolve to 2
        // The constraint check should catch this
        assert!(
            !sub.check_constraints(&constraints, &heap),
            "Constraints should detect same binding through deref chains"
        );
    }

    /// Test that constraints don't falsely trigger on non-constrained bindings
    #[test]
    fn test_constraints_ignore_non_constrained() {
        let (p, _, _, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0
            (Tag::Ref, 1),      // 1
            (Tag::Ref, 2),      // 2
            (Tag::Con, p),      // 3
        ];
        
        // Only constrain addresses 0 and 1
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        let mut sub = Substitution::default();
        // Bind non-constrained refs to same address - should be OK
        sub = sub.push((2, 3, false));
        sub = sub.push((0, 3, false));  // Constrained, but 1 is not bound
        
        assert!(
            sub.check_constraints(&constraints, &heap),
            "Should pass when only one constrained var is bound"
        );
    }

    // ============================================================================
    // TEST CATEGORY 3: ENVIRONMENT UNDO MECHANICS
    // ============================================================================

    /// Test that undo_try properly restores hypothesis state
    #[test]
    fn test_undo_try_removes_hypothesis_clause() {
        let (p, q, _, a, b) = setup_symbols();
        
        let mut heap: Arc<Vec<Cell>> = Arc::new(vec![
            (Tag::Func, 2),     // 0
            (Tag::Con, p),      // 1
            (Tag::Con, a),      // 2
        ]);
        
        let mut heap = QueryHeap::new(heap.clone(), None).unwrap();

        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Create an environment that added a clause
        let mut env = Env::new(0, 0);
        env.new_clause = true;
        env.invent_pred = true;
        env.bindings = Box::new([]);
        env.children = 0;
        
        // Add a clause to hypothesis (simulating what try_choices does)
        let clause = Clause::new(vec![0], None);
        hypothesis.push_clause(clause, &heap, vec![].into());
        h_clauses = 1;
        invented_preds = 1;
        
        assert_eq!(hypothesis.len(), 1);
        
        // Undo should remove the clause
        let children = env.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        assert_eq!(hypothesis.len(), 0, "Clause should be removed from hypothesis");
        assert_eq!(h_clauses, 0, "h_clauses counter should be decremented");
        assert_eq!(invented_preds, 0, "invented_preds should be decremented");
        assert!(!env.new_clause, "new_clause flag should be reset");
        assert!(!env.invent_pred, "invent_pred flag should be reset");
    }

    /// Test that undo_try properly unbinds
    #[test]
    fn test_undo_try_unbinds() {
        let (p, _, _, a, _) = setup_symbols();
        
        let heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(heap.clone(), None).unwrap();
            heap.heap_push((Tag::Ref, 0));
            heap.heap_push((Tag::Con, a));

        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Bind ref 0 to const at 1
        let bindings = vec![(0usize, 1usize)];
        heap.bind(&bindings);
        
        let mut env = Env::new(0, 0);
        env.bindings = bindings.into_boxed_slice();
        env.new_clause = false;
        env.children = 2;
        
        assert_eq!(heap[0], (Tag::Ref, 1), "Ref should be bound before undo");
        
        let children = env.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        assert!(is_unbound_ref(&heap, 0), "Ref should be unbound after undo");
        assert_eq!(children, 2, "Should return correct children count");
    }

    // ============================================================================
    // TEST CATEGORY 4: CONSTRAINT COLLECTION FROM META-CLAUSES
    // ============================================================================

    /// Test that constraints are correctly collected from meta-vars
    #[test]
    fn test_constraint_collection_from_meta_vars() {
        let (p, q, _, _, _) = setup_symbols();
        
        // Create a meta-clause: P(X,Y) :- Q(X,Y) with P,Q as meta-vars
        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);  // P is meta-var (arg 0)
        meta_vars.set(1);  // Q is meta-var (arg 1)
        
        let clause = Clause::new(
            vec![0, 4],  // head at 0, body at 4
            Some(vec![0, 1])
        );
        
        assert!(clause.meta(), "Should be recognized as meta clause");
        assert!(clause.meta_var(0).unwrap(), "Arg 0 should be meta-var");
        assert!(clause.meta_var(1).unwrap(), "Arg 1 should be meta-var");
        assert!(!clause.meta_var(2).unwrap(), "Arg 2 should not be meta-var");
    }

    /// Test constraint propagation through hypothesis
    #[test]
    fn test_hypothesis_constraints_accumulate() {
        let (p, q, r, a, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Func, 2),     // 0
            (Tag::Con, p),      // 1
            (Tag::Ref, 2),      // 2
        ];
        
        let mut hypothesis = Hypothesis::new();
        
        // Add clause with constraints [0, 1]
        let clause1 = Clause::new(vec![0], None);
        hypothesis.push_clause(clause1, &heap, vec![0, 1].into());
        
        // Add another clause with constraints [2, 3]
        let clause2 = Clause::new(vec![0], None);
        hypothesis.push_clause(clause2, &heap, vec![2, 3].into());
        
        assert_eq!(hypothesis.constraints.len(), 2);
        assert_eq!(&*hypothesis.constraints[0], &[0, 1]);
        assert_eq!(&*hypothesis.constraints[1], &[2, 3]);
        
        // Pop should remove last constraint
        hypothesis.pop_clause();
        assert_eq!(hypothesis.constraints.len(), 1);
    }

    // ============================================================================
    // TEST CATEGORY 5: SUBSTITUTION INTEGRITY
    // ============================================================================

    /// Test get_bindings returns correct subset
    #[test]
    fn test_substitution_get_bindings() {
        let mut sub = Substitution::default();
        
        sub = sub.push((0, 10, false));
        sub = sub.push((1, 20, true));
        sub = sub.push((2, 30, false));
        
        let bindings = sub.get_bindings();
        
        assert_eq!(bindings.len(), 3);
        assert_eq!(bindings[0], (0, 10));
        assert_eq!(bindings[1], (1, 20));
        assert_eq!(bindings[2], (2, 30));
    }

    /// Test that arg registers don't leak between resolutions
    #[test]
    fn test_arg_registers_isolation() {
        let sub1 = Substitution::default();
        
        // Set arg 0 in sub1
        let mut sub1 = Substitution::default();
        sub1.set_arg(0, 100);
        sub1.set_arg(5, 500);
        
        assert_eq!(sub1.get_arg(0), Some(100));
        assert_eq!(sub1.get_arg(5), Some(500));
        assert_eq!(sub1.get_arg(1), None);
        
        // A new substitution should have clean registers
        let sub2 = Substitution::default();
        assert_eq!(sub2.get_arg(0), None);
        assert_eq!(sub2.get_arg(5), None);
    }

    // ============================================================================
    // TEST CATEGORY 6: COMPLEX SCENARIOS
    // ============================================================================

    /// Test the chain meta-rule scenario: P(x,y) :- Q(x,z), R(z,y)
    /// This tests that P, Q, R cannot all be bound to the same predicate
    #[test]
    fn test_chain_metarule_constraints() {
        let (p, q, r, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Con, p),      // 0: 'p'
            (Tag::Con, q),      // 1: 'q'  
            (Tag::Con, r),      // 2: 'r'
            (Tag::Ref, 3),      // 3: P (meta-var)
            (Tag::Ref, 4),      // 4: Q (meta-var)
            (Tag::Ref, 5),      // 5: R (meta-var)
        ];
        
        // Constraints: P, Q, R (addresses 3, 4, 5) cannot share values
        let constraints: Arc<[usize]> = vec![3, 4, 5].into();
        
        // Scenario 1: All different - should pass
        let mut sub = Substitution::default();
        sub = sub.push((3, 0, false));  // P -> 'p'
        sub = sub.push((4, 1, false));  // Q -> 'q'
        sub = sub.push((5, 2, false));  // R -> 'r'
        assert!(sub.check_constraints(&constraints, &heap), "All different should pass");
        
        // Scenario 2: P == Q - should fail
        let mut sub = Substitution::default();
        sub = sub.push((3, 0, false));  // P -> 'p'
        sub = sub.push((4, 0, false));  // Q -> 'p' (same!)
        sub = sub.push((5, 2, false));  // R -> 'r'
        assert!(!sub.check_constraints(&constraints, &heap), "P == Q should fail");
        
        // Scenario 3: Q == R - should fail
        let mut sub = Substitution::default();
        sub = sub.push((3, 0, false));  // P -> 'p'
        sub = sub.push((4, 1, false));  // Q -> 'q'
        sub = sub.push((5, 1, false));  // R -> 'q' (same as Q!)
        assert!(!sub.check_constraints(&constraints, &heap), "Q == R should fail");
    }

    /// Test tailrec scenario: P(x,y) :- Q(x,z), P(z,y)
    /// P can equal itself (recursion), but P != Q
    #[test]
    fn test_tailrec_metarule_constraints() {
        let (p, q, _, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Con, p),      // 0: 'p'
            (Tag::Con, q),      // 1: 'q'
            (Tag::Ref, 2),      // 2: P (head)
            (Tag::Ref, 3),      // 3: Q (body first)
            (Tag::Ref, 4),      // 4: P (body second, same as head - OK for recursion)
        ];
        
        // For tailrec, constraint is only between P and Q (indices 2 and 3)
        // The second P (index 4) should unify with head P
        let constraints: Arc<[usize]> = vec![2, 3].into();
        
        // P != Q should pass
        let mut sub = Substitution::default();
        sub = sub.push((2, 0, false));  // P -> 'p'
        sub = sub.push((3, 1, false));  // Q -> 'q'
        // Note: 4 would be unified with 2 during resolution, not bound separately
        assert!(sub.check_constraints(&constraints, &heap), "P != Q should pass");
        
        // P == Q should fail
        let mut sub = Substitution::default();
        sub = sub.push((2, 0, false));  // P -> 'p'
        sub = sub.push((3, 0, false));  // Q -> 'p' (same!)
        assert!(!sub.check_constraints(&constraints, &heap), "P == Q should fail for tailrec");
    }

    /// Test that re_build_bound_arg_terms correctly handles complex terms
    #[test]
    fn test_rebuild_bound_arg_terms() {
        let (p, _, _, a, b) = setup_symbols();
        
        let mut heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: To be bound to complex term at 4
            (Tag::Ref, 1),      // 1: Simple binding target
            (Tag::Con, a),      // 2
            (Tag::Con, b),      // 3
            (Tag::Func, 3),     // 4: f(Arg0, Arg1)
            (Tag::Con, p),      // 5
            (Tag::Arg, 0),      // 6
            (Tag::Arg, 1),      // 7
        ];
        
        let mut sub = Substitution::default();
        sub = sub.push((0, 4, true));   // Ref 0 bound to complex term (marked true)
        sub = sub.push((1, 2, false));  // Ref 1 bound to simple term
        sub.set_arg(0, 2);  // Arg0 -> 'a'
        sub.set_arg(1, 3);  // Arg1 -> 'b'
        
        let old_len = heap.heap_len();
        re_build_bound_arg_terms(&mut heap, &mut sub);
        
        // After rebuild, ref 0 should be bound to a newly built term
        // The new term should have refs instead of args
        assert!(heap.heap_len() > old_len, "New term should be built");
        
        // The bound address should be updated
        assert_ne!(sub[0].1, 4, "Bound address should be updated to new term");
    }

    // ============================================================================
    // TEST CATEGORY 7: EDGE CASES AND POTENTIAL BUGS
    // ============================================================================

    /// Test empty bindings list doesn't cause issues
    #[test]
    fn test_empty_bindings_undo() {
        let mut heap: Vec<Cell> = vec![(Tag::Ref, 0)];
        
        let bindings: Vec<(usize, usize)> = vec![];
        heap.bind(&bindings);
        heap.unbind(&bindings);
        
        assert!(is_unbound_ref(&heap, 0));
    }

    /// Test constraint check with empty constraints
    #[test]
    fn test_empty_constraints() {
        let heap: Vec<Cell> = vec![(Tag::Ref, 0)];
        let constraints: Arc<[usize]> = vec![].into();
        
        let mut sub = Substitution::default();
        sub = sub.push((0, 0, false));
        
        assert!(sub.check_constraints(&constraints, &heap), "Empty constraints should always pass");
    }

    /// Test single constraint
    #[test]
    fn test_single_constraint() {
        let (_, _, _, a, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),
            (Tag::Con, a),
        ];
        let constraints: Arc<[usize]> = vec![0].into();
        
        let mut sub = Substitution::default();
        sub = sub.push((0, 1, false));
        
        // Single constraint can't conflict with itself
        assert!(sub.check_constraints(&constraints, &heap), "Single constraint should pass");
    }

    /// Test that hypothesis pop removes matching constraint
    #[test]
    fn test_hypothesis_constraint_pop_order() {
        let heap: Vec<Cell> = vec![];
        let mut hypothesis = Hypothesis::new();
        
        let c1 = Clause::new(vec![], None);
        let c2 = Clause::new(vec![], None);
        let c3 = Clause::new(vec![], None);
        
        hypothesis.push_clause(c1, &heap, vec![1].into());
        hypothesis.push_clause(c2, &heap, vec![2].into());
        hypothesis.push_clause(c3, &heap, vec![3].into());
        
        assert_eq!(hypothesis.constraints.len(), 3);
        
        hypothesis.pop_clause();
        assert_eq!(hypothesis.constraints.len(), 2);
        assert_eq!(&*hypothesis.constraints[1], &[2]);
        
        hypothesis.pop_clause();
        assert_eq!(hypothesis.constraints.len(), 1);
        assert_eq!(&*hypothesis.constraints[0], &[1]);
    }

    /// Test constraint check when both bindings point to refs that need dereferencing
    #[test]
    fn test_constraints_double_deref() {
        let (p, _, _, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 1),      // 0: -> 1
            (Tag::Ref, 4),      // 1: -> 4 (target: Con p)
            (Tag::Ref, 3),      // 2: -> 3
            (Tag::Ref, 4),      // 3: -> 4 (same target!)
            (Tag::Con, p),      // 4: 'p'
        ];
        
        let constraints: Arc<[usize]> = vec![0, 2].into();
        
        let mut sub = Substitution::default();
        // Both 0 and 2 ultimately deref to 4
        sub = sub.push((0, 1, false));
        sub = sub.push((2, 3, false));
        
        assert!(
            !sub.check_constraints(&constraints, &heap),
            "Should detect same target through double deref"
        );
    }

    /// Test that retrying doesn't leave stale constraint references
    #[test]
    fn test_retry_constraint_cleanup() {
        let (p, q, _, _, _) = setup_symbols();
        
        let heap: Vec<Cell> = vec![
            (Tag::Con, p),
            (Tag::Con, q),
        ];
        
        let mut hypothesis = Hypothesis::new();
        
        // Simulate: add clause, then undo
        let clause = Clause::new(vec![], None);
        hypothesis.push_clause(clause.clone(), &heap, vec![0, 1].into());
        
        assert_eq!(hypothesis.len(), 1);
        assert_eq!(hypothesis.constraints.len(), 1);
        
        // Simulate undo
        hypothesis.pop_clause();
        
        assert_eq!(hypothesis.len(), 0);
        assert_eq!(hypothesis.constraints.len(), 0, "Constraints should also be removed");
        
        // Add different clause
        hypothesis.push_clause(clause, &heap, vec![1].into());
        
        assert_eq!(hypothesis.constraints.len(), 1);
        assert_eq!(&*hypothesis.constraints[0], &[1], "Should have new constraints, not old");
    }
}
