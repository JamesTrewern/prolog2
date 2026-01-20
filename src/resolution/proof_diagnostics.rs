/// Diagnostic tests and helpers for debugging the proof loop
/// 
/// These tests provide detailed tracing of what happens during resolution
/// to help identify where logical errors occur.

#[cfg(test)]
mod proof_diagnostics {
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
        },
        resolution::{
            unification::{unify, Substitution},
            build::{build, re_build_bound_arg_terms},
        },
    };

    // ============================================================================
    // DIAGNOSTIC HELPERS
    // ============================================================================

    /// Trace the state of relevant heap addresses
    fn trace_heap_state(heap: &impl Heap, addresses: &[usize], label: &str) {
        println!("\n=== {} ===", label);
        for &addr in addresses {
            let cell = heap[addr];
            let deref = heap.deref_addr(addr);
            let term_str = heap.term_string(addr);
            println!(
                "  [{}]: {:?} -> deref={} -> \"{}\"",
                addr, cell, deref, term_str
            );
        }
    }

    /// Trace substitution state
    fn trace_substitution(sub: &Substitution, label: &str) {
        println!("\n=== {} ===", label);
        for i in 0..32 {
            if let Some(addr) = sub.get_arg(i) {
                println!("  Arg{} -> {}", i, addr);
            }
        }
        println!("  Bindings: {:?}", sub.get_bindings());
    }

    /// Trace hypothesis state
    fn trace_hypothesis(hyp: &Hypothesis, heap: &impl Heap, label: &str) {
        println!("\n=== {} ===", label);
        println!("  Clauses: {}", hyp.len());
        for (i, clause) in hyp.iter().enumerate() {
            println!("    [{}]: {}", i, clause.to_string(heap));
        }
        println!("  Constraints: {:?}", hyp.constraints);
    }

    // ============================================================================
    // TEST: Trace unification through deref chains
    // ============================================================================

    #[test]
    fn trace_unification_with_derefs() {
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());

        // Create a scenario with reference chains
        let heap: Vec<Cell> = vec![
            // Clause head: P(X,Y) at addresses 0-4
            (Tag::Func, 3),     // 0
            (Tag::Arg, 0),      // 1: P (meta-var)
            (Tag::Arg, 1),      // 2: X
            (Tag::Arg, 2),      // 3: Y
            
            // Goal: p(a,b) at addresses 4-7
            (Tag::Func, 3),     // 4
            (Tag::Con, p),      // 5: 'p'
            (Tag::Con, a),      // 6: 'a'
            (Tag::Con, b),      // 7: 'b'
        ];

        println!("Heap before unification:");
        trace_heap_state(&heap, &[0, 1, 2, 3, 4, 5, 6, 7], "Initial");

        // Unify clause head (0) with goal (4)
        let sub = unify(&heap, 0, 4);
        
        match sub {
            Some(sub) => {
                trace_substitution(&sub, "After Unification");
                
                // Verify meta-var P (Arg0) is bound to 'p' (addr 5)
                assert_eq!(sub.get_arg(0), Some(5), "P should be bound to 'p'");
                // Verify X (Arg1) is bound to 'a' (addr 6)
                assert_eq!(sub.get_arg(1), Some(6), "X should be bound to 'a'");
                // Verify Y (Arg2) is bound to 'b' (addr 7)
                assert_eq!(sub.get_arg(2), Some(7), "Y should be bound to 'b'");
            }
            None => panic!("Unification should succeed"),
        }
    }

    // ============================================================================
    // TEST: Trace build with meta-vars
    // ============================================================================

    #[test]
    fn trace_build_with_meta_vars() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());

        let mut heap: Vec<Cell> = vec![
            // Meta-clause body literal: Q(X,Y) at addresses 0-3
            (Tag::Func, 3),     // 0
            (Tag::Arg, 1),      // 1: Q (meta-var, arg 1)
            (Tag::Arg, 2),      // 2: X (first-order var, arg 2)
            (Tag::Arg, 3),      // 3: Y (first-order var, arg 3)
            
            // Constants for binding
            (Tag::Con, p),      // 4: 'p'
            (Tag::Con, q),      // 5: 'q'
            (Tag::Con, a),      // 6: 'a'
            (Tag::Con, b),      // 7: 'b'
        ];

        // Create substitution
        let mut sub = Substitution::default();
        sub.set_arg(1, 5);  // Q -> 'q'
        sub.set_arg(2, 6);  // X -> 'a'
        sub.set_arg(3, 7);  // Y -> 'b'

        // Create meta_vars bitflag - args 0 and 1 are meta-vars
        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);  // P is meta-var (even though not in this term)
        meta_vars.set(1);  // Q is meta-var

        trace_substitution(&sub, "Before Build");
        trace_heap_state(&heap, &[0, 1, 2, 3], "Clause term before build");

        let heap_len_before = heap.heap_len();
        let new_addr = build(&mut heap, &mut sub, Some(meta_vars), 0);

        println!("\n=== After Build ===");
        println!("  Built new term at address: {}", new_addr);
        println!("  Heap grew from {} to {} cells", heap_len_before, heap.heap_len());
        println!("  New term: {}", heap.term_string(new_addr));
        
        trace_heap_state(&heap, &(heap_len_before..heap.heap_len()).collect::<Vec<_>>(), "New heap cells");
    }

    // ============================================================================
    // TEST: Trace constraint violation detection
    // ============================================================================

    #[test]
    fn trace_constraint_violation() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());

        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Query ref for P
            (Tag::Ref, 1),      // 1: Query ref for Q
            (Tag::Con, p),      // 2: 'p'
            (Tag::Con, q),      // 3: 'q'
        ];

        // Constraints: refs at 0 and 1 shouldn't both bind to same target
        let constraints: Arc<[usize]> = vec![0, 1].into();

        println!("\n=== Constraint Test ===");
        println!("Constraints: addresses {:?} should not share targets", &*constraints);

        // Test 1: Both bound to same target (should fail)
        let mut sub1 = Substitution::default();
        sub1 = sub1.push((0, 2, false));
        sub1 = sub1.push((1, 2, false));  // Same as above!

        println!("\nTest 1: Both refs bound to addr 2 ('p')");
        println!("  Binding 0: 0 -> 2");
        println!("  Binding 1: 1 -> 2");
        
        let result1 = sub1.check_constraints(&constraints, &heap);
        println!("  Result: {} (expected: false)", result1);

        // Detailed trace of what check_constraints is actually checking
        println!("  Detailed check:");
        for (src, tgt, _) in sub1.iter() {
            let deref_src = heap.deref_addr(*src);
            let deref_tgt = heap.deref_addr(*tgt);
            println!(
                "    binding ({}, {}): deref_src={}, deref_tgt={}, src_in_constraints={}, tgt_in_constraints={}",
                src, tgt, deref_src, deref_tgt,
                constraints.contains(&deref_src),
                constraints.contains(&deref_tgt)
            );
        }

        // Test 2: Bound to different targets (should pass)
        let mut sub2 = Substitution::default();
        sub2 = sub2.push((0, 2, false));  // -> 'p'
        sub2 = sub2.push((1, 3, false));  // -> 'q'

        println!("\nTest 2: Refs bound to different targets");
        println!("  Binding 0: 0 -> 2 ('p')");
        println!("  Binding 1: 1 -> 3 ('q')");
        
        let result2 = sub2.check_constraints(&constraints, &heap);
        println!("  Result: {} (expected: true)", result2);
    }

    // ============================================================================
    // TEST: Trace full resolution step
    // ============================================================================

    #[test]
    fn trace_full_resolution_step() {
        let ancestor = SymbolDB::set_const("ancestor".into());
        let parent = SymbolDB::set_const("parent".into());
        let a = SymbolDB::set_const("alice".into());
        let b = SymbolDB::set_const("bob".into());

        println!("\n========================================");
        println!("FULL RESOLUTION STEP TRACE");
        println!("========================================");
        println!("\nScenario: Learning ancestor definition");
        println!("Goal: ancestor(alice, bob)");
        println!("Meta-clause: P(X,Y) :- Q(X,Y)");

        let mut heap: Vec<Cell> = vec![
            // Goal: ancestor(alice, bob) at 0-3
            (Tag::Func, 3),         // 0
            (Tag::Con, ancestor),   // 1
            (Tag::Con, a),          // 2: alice
            (Tag::Con, b),          // 3: bob
            
            // Meta-clause head: P(X,Y) at 4-7
            (Tag::Func, 3),         // 4
            (Tag::Arg, 0),          // 5: P (meta-var)
            (Tag::Arg, 1),          // 6: X
            (Tag::Arg, 2),          // 7: Y
            
            // Meta-clause body: Q(X,Y) at 8-11
            (Tag::Func, 3),         // 8
            (Tag::Arg, 3),          // 9: Q (meta-var)
            (Tag::Arg, 1),          // 10: X (shared with head)
            (Tag::Arg, 2),          // 11: Y (shared with head)
            
            // Available predicates
            (Tag::Con, parent),     // 12: parent
        ];

        trace_heap_state(&heap, &(0..13).collect::<Vec<_>>(), "Initial Heap");

        println!("\n--- Step 1: Unify goal with clause head ---");
        let sub = unify(&heap, 4, 0);
        
        match sub {
            Some(mut sub) => {
                trace_substitution(&sub, "Substitution after unify(head, goal)");
                
                println!("\n--- Step 2: Build new body goal ---");
                let body_addr = build(&mut heap, &mut sub, None, 8);
                println!("Built body goal at addr {}: {}", body_addr, heap.term_string(body_addr));
                
                println!("\n--- Step 3: Build hypothesis clause ---");
                // Build head with meta_vars flagged
                let mut meta_vars = BitFlag64::default();
                meta_vars.set(0);  // P is meta-var
                meta_vars.set(3);  // Q is meta-var
                
                // Simulate inventing predicate (P bound to new symbol)
                let invented_pred = SymbolDB::set_const("pred_0".into());
                let invented_addr = heap.set_const(invented_pred);
                sub.set_arg(0, invented_addr);
                
                println!("Invented predicate at addr {}", invented_addr);
                
                let new_head = build(&mut heap, &mut sub, Some(meta_vars), 4);
                let new_body = build(&mut heap, &mut sub, Some(meta_vars), 8);
                
                println!("New clause head: {}", heap.term_string(new_head));
                println!("New clause body: {}", heap.term_string(new_body));
                
                println!("\n--- Step 4: Collect constraints ---");
                let mut constraints = Vec::new();
                for i in 0..32 {
                    if meta_vars.get(i) {
                        if let Some(addr) = sub.get_arg(i) {
                            constraints.push(addr);
                            println!("Constraint: Arg{} bound to addr {}", i, addr);
                        }
                    }
                }
                println!("Final constraints: {:?}", constraints);

                println!("\n--- Final heap state ---");
                trace_heap_state(&heap, &(0..heap.heap_len()).collect::<Vec<_>>(), "Final Heap");
            }
            None => panic!("Unification should succeed"),
        }
    }

    // ============================================================================
    // TEST: Trace retry behavior
    // ============================================================================

    #[test]
    fn trace_retry_behavior() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Query ref
            (Tag::Ref, 1),      // 1: Query ref
            (Tag::Con, p),      // 2
            (Tag::Con, a),      // 3
        ];

        println!("\n========================================");
        println!("RETRY BEHAVIOR TRACE");
        println!("========================================");

        let mut hypothesis = Hypothesis::new();

        println!("\n--- Initial state ---");
        trace_heap_state(&heap, &[0, 1], "Heap refs");
        trace_hypothesis(&hypothesis, &heap, "Hypothesis");

        println!("\n--- Simulating successful try ---");
        let bindings = vec![(0usize, 2usize), (1usize, 3usize)];
        heap.bind(&bindings);
        
        let dummy_head = heap.heap_push((Tag::Con, p));
        let clause = Clause::new(vec![dummy_head], None);
        hypothesis.push_clause(clause, &heap, vec![0, 1].into());

        trace_heap_state(&heap, &[0, 1], "After bind");
        trace_hypothesis(&hypothesis, &heap, "After add clause");

        println!("\n--- Simulating undo (retry) ---");
        // This is what undo_try does:
        hypothesis.pop_clause();
        heap.unbind(&bindings);

        trace_heap_state(&heap, &[0, 1], "After unbind");
        trace_hypothesis(&hypothesis, &heap, "After remove clause");

        // Verify state is restored
        assert_eq!(heap[0], (Tag::Ref, 0), "Ref 0 should be self-referencing");
        assert_eq!(heap[1], (Tag::Ref, 1), "Ref 1 should be self-referencing");
        assert_eq!(hypothesis.len(), 0, "Hypothesis should be empty");
        assert_eq!(hypothesis.constraints.len(), 0, "Constraints should be empty");

        println!("\n=== Retry successful: state properly restored ===");
    }
}
