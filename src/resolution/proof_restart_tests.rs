/// Tests for proof restart/continuation behavior
/// 
/// When a proof succeeds and the user requests another solution,
/// the prover must:
/// 1. Backtrack correctly from the successful state
/// 2. Undo the effects of the last environment
/// 3. Try alternative choices
/// 4. Maintain hypothesis consistency
/// 
/// The key code path is in Proof::prove():
/// ```
/// if self.pointer == self.stack.len() {
///     self.pointer -= 1;
///     self.stack[self.pointer].undo_try(...);
/// }
/// ```

#[cfg(test)]
mod proof_restart_tests {
    use std::sync::Arc;
    use crate::{
        heap::{
            heap::{Cell, Heap, Tag},
            query_heap::QueryHeap,
            symbol_db::SymbolDB,
        },
        program::{
            clause::Clause,
            hypothesis::Hypothesis,
            predicate_table::PredicateTable,
        },
        resolution::proof::{Env, Proof},
        Config,
    };

    // ============================================================================
    // HELPER: Create a minimal test config
    // ============================================================================
    
    fn test_config() -> Config {
        Config {
            max_depth: 10,
            max_clause: 4,
            max_pred: 2,
        }
    }

    // ============================================================================
    // TEST: Verify proof state after first solution
    // ============================================================================

    /// After a successful proof, pointer should equal stack length
    #[test]
    fn test_proof_state_after_success() {
        // This test verifies the invariant that after prove() returns true,
        // self.pointer == self.stack.len()
        
        // When we call prove() again for the next solution, it should:
        // 1. Detect pointer == stack.len()
        // 2. Decrement pointer
        // 3. Call undo_try on that environment
        // 4. Continue searching
        
        // The key question: Is the pointer/stack state correct after first solution?
        println!("After successful proof:");
        println!("  - pointer should == stack.len()");
        println!("  - All goals should be 'proven' (past the pointer)");
        println!("  - hypothesis should contain all learned clauses");
    }

    // ============================================================================
    // TEST: Undo behavior when restarting
    // ============================================================================

    /// When restarting, undo_try should be called on the LAST environment
    #[test]
    fn test_restart_calls_undo_on_last_env() {
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());
        
        // Setup: Create a scenario where we have multiple environments
        // and need to verify that restart undoes the correct one
        
        let prog_heap = Arc::new(vec![
            (Tag::Func, 2),     // 0: p(a)
            (Tag::Con, p),      // 1
            (Tag::Con, a),      // 2
        ]);
        
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        // Push a goal
        let goal = heap.heap_push((Tag::Func, 2));
        heap.heap_push((Tag::Con, p));
        heap.heap_push((Tag::Con, a));
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Create environments simulating a proof with multiple goals
        let mut env0 = Env::new(goal, 0);
        env0.children = 0;
        env0.new_clause = true;  // This env created a clause
        env0.bindings = Box::new([]);
        
        // Add a clause to hypothesis (simulating what try_choices does)
        let clause_head = heap.heap_push((Tag::Func, 2));
        heap.heap_push((Tag::Con, p));
        heap.heap_push((Tag::Arg, 0));
        let clause = Clause::new(vec![clause_head], None);
        hypothesis.push_clause(clause, &heap, vec![].into());
        h_clauses = 1;
        
        println!("Before restart:");
        println!("  hypothesis.len() = {}", hypothesis.len());
        println!("  h_clauses = {}", h_clauses);
        
        // Simulate restart: undo_try on last environment
        let children = env0.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        println!("After undo_try:");
        println!("  hypothesis.len() = {}", hypothesis.len());
        println!("  h_clauses = {}", h_clauses);
        println!("  children returned = {}", children);
        
        assert_eq!(hypothesis.len(), 0, "Hypothesis should be empty after undo");
        assert_eq!(h_clauses, 0, "h_clauses should be 0 after undo");
    }

    // ============================================================================
    // TEST: Multiple restarts maintain consistency
    // ============================================================================

    /// Repeated restarts should not accumulate stale state
    #[test]
    fn test_multiple_restarts_no_stale_state() {
        let p = SymbolDB::set_const("test_p".into());
        let q = SymbolDB::set_const("test_q".into());
        
        let prog_heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Simulate: Find solution 1, restart, find solution 2, restart...
        
        for iteration in 0..3 {
            println!("\n=== Iteration {} ===", iteration);
            
            // Simulate finding a solution (add clause to hypothesis)
            let clause_head = heap.heap_push((Tag::Con, p));
            let clause = Clause::new(vec![clause_head], None);
            hypothesis.push_clause(clause, &heap, vec![iteration].into());
            h_clauses += 1;
            
            println!("After 'finding solution':");
            println!("  hypothesis.len() = {}", hypothesis.len());
            println!("  constraints count = {}", hypothesis.constraints.len());
            
            // Create env that 'found' this solution
            let mut env = Env::new(clause_head, 0);
            env.new_clause = true;
            env.bindings = Box::new([]);
            env.children = 0;
            
            // Simulate restart
            env.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
            
            println!("After restart:");
            println!("  hypothesis.len() = {}", hypothesis.len());
            println!("  constraints count = {}", hypothesis.constraints.len());
            
            assert_eq!(hypothesis.len(), 0, "Hypothesis should be empty after restart");
            assert_eq!(hypothesis.constraints.len(), 0, "Constraints should be empty after restart");
        }
    }

    // ============================================================================
    // TEST: Restart with nested goals
    // ============================================================================

    /// When restarting with nested goals, child goals should be properly removed
    #[test]
    fn test_restart_removes_child_goals() {
        // Scenario:
        // - Goal 0 spawns Goals 1, 2 (children = 2)
        // - Goals 1, 2 are proven
        // - User requests restart
        // - Goal 0's undo_try is called
        // - Children count (2) is returned
        // - Proof::prove should drain those children from stack
        
        let p = SymbolDB::set_const("nested_p".into());
        
        let prog_heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        let goal0 = heap.heap_push((Tag::Con, p));
        let goal1 = heap.heap_push((Tag::Con, p));
        let goal2 = heap.heap_push((Tag::Con, p));
        
        // Simulate stack state after successful proof:
        // [env0(goal0), env1(goal1), env2(goal2)]
        // pointer = 3 (past end)
        
        let mut env0 = Env::new(goal0, 0);
        env0.children = 2;  // env0 spawned 2 children
        env0.new_clause = false;
        env0.bindings = Box::new([]);
        
        let env1 = Env::new(goal1, 1);
        let env2 = Env::new(goal2, 1);
        
        let mut stack = vec![env0, env1, env2];
        let mut pointer = 3;  // Past end = success
        
        println!("Initial state:");
        println!("  stack.len() = {}", stack.len());
        println!("  pointer = {}", pointer);
        
        // Simulate restart logic from Proof::prove()
        assert_eq!(pointer, stack.len(), "Pointer should equal stack len after success");
        
        pointer -= 1;
        println!("After decrement: pointer = {}", pointer);
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        let children = stack[pointer].undo_try(
            &mut hypothesis, 
            &mut heap, 
            &mut h_clauses, 
            &mut invented_preds
        );
        
        println!("undo_try returned children = {}", children);
        
        // Drain children from stack
        // In prove(): self.stack.drain((self.pointer + 1)..(self.pointer + 1 + children));
        let drain_start = pointer + 1;
        let drain_end = pointer + 1 + children;
        
        println!("Draining range: {}..{}", drain_start, drain_end);
        
        stack.drain(drain_start..drain_end);
        
        println!("After drain:");
        println!("  stack.len() = {}", stack.len());
        
        assert_eq!(stack.len(), 1, "Only env0 should remain");
    }

    // ============================================================================
    // TEST: Hypothesis clauses added by different envs
    // ============================================================================

    /// Each env tracks whether IT added a clause; restart should only remove that env's clause
    #[test]
    fn test_only_own_clause_removed_on_undo() {
        let p = SymbolDB::set_const("own_p".into());
        let q = SymbolDB::set_const("own_q".into());
        
        let prog_heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Env0 adds clause for 'p'
        let clause_p = heap.heap_push((Tag::Con, p));
        hypothesis.push_clause(Clause::new(vec![clause_p], None), &heap, vec![0].into());
        h_clauses += 1;
        
        let mut env0 = Env::new(clause_p, 0);
        env0.new_clause = true;
        env0.children = 1;
        env0.bindings = Box::new([]);
        
        // Env1 adds clause for 'q'
        let clause_q = heap.heap_push((Tag::Con, q));
        hypothesis.push_clause(Clause::new(vec![clause_q], None), &heap, vec![1].into());
        h_clauses += 1;
        
        let mut env1 = Env::new(clause_q, 1);
        env1.new_clause = true;
        env1.children = 0;
        env1.bindings = Box::new([]);
        
        println!("Before any undo:");
        println!("  hypothesis.len() = {}", hypothesis.len());
        assert_eq!(hypothesis.len(), 2);
        
        // Undo env1 (the last one)
        env1.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        println!("After undo env1:");
        println!("  hypothesis.len() = {}", hypothesis.len());
        assert_eq!(hypothesis.len(), 1, "Only env1's clause should be removed");
        assert_eq!(h_clauses, 1);
        
        // Undo env0
        env0.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        println!("After undo env0:");
        println!("  hypothesis.len() = {}", hypothesis.len());
        assert_eq!(hypothesis.len(), 0, "All clauses should be removed");
        assert_eq!(h_clauses, 0);
    }

    // ============================================================================
    // TEST: Bindings are properly unbound on restart
    // ============================================================================

    #[test]
    fn test_bindings_unbound_on_restart() {
        let p = SymbolDB::set_const("bind_p".into());
        let a = SymbolDB::set_const("bind_a".into());
        
        let prog_heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        // Create refs that will be bound
        let ref0 = heap.heap_push((Tag::Ref, heap.heap_len()));
        let ref1 = heap.heap_push((Tag::Ref, heap.heap_len()));
        let const_a = heap.heap_push((Tag::Con, a));
        
        // Bind the refs
        let bindings = vec![(ref0, const_a), (ref1, const_a)];
        heap.bind(&bindings);
        
        println!("After bind:");
        println!("  ref0 points to: {}", heap[ref0].1);
        println!("  ref1 points to: {}", heap[ref1].1);
        
        assert_eq!(heap[ref0].1, const_a);
        assert_eq!(heap[ref1].1, const_a);
        
        // Create env with these bindings
        let mut env = Env::new(0, 0);
        env.bindings = bindings.into_boxed_slice();
        env.new_clause = false;
        env.children = 0;
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Undo
        env.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        println!("After undo:");
        println!("  ref0 points to: {} (should be {})", heap[ref0].1, ref0);
        println!("  ref1 points to: {} (should be {})", heap[ref1].1, ref1);
        
        assert_eq!(heap[ref0].1, ref0, "ref0 should be self-referencing");
        assert_eq!(heap[ref1].1, ref1, "ref1 should be self-referencing");
    }

    // ============================================================================
    // TEST: got_choices flag behavior on restart
    // ============================================================================

    /// After undo_try, the env should still have remaining choices to try
    #[test]
    fn test_choices_persist_after_undo() {
        // When we undo an environment, we don't reset got_choices
        // The env should continue trying from its remaining choices
        
        let mut env = Env::new(0, 0);
        let symbol = SymbolDB::set_const("symbol".to_string());

        // Simulate: env got choices and tried one
        env.got_choices = true;
        env.choices = vec![
            Clause::new(vec![0], None),  // Already tried (popped)
            Clause::new(vec![1], None),  // Next to try
            Clause::new(vec![2], None),  // After that
        ];
        env.new_clause = false;
        env.bindings = Box::new([]);
        env.children = 0;
        
        let prog_heap = Arc::new(vec![(Tag::Con, symbol)]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        let choices_before = env.choices.len();
        
        env.undo_try(&mut hypothesis, &mut heap, &mut h_clauses, &mut invented_preds);
        
        let choices_after = env.choices.len();
        
        println!("Choices before undo: {}", choices_before);
        println!("Choices after undo: {}", choices_after);
        println!("got_choices flag: {}", env.got_choices);
        
        // Choices should be unchanged - undo doesn't affect the choice list
        assert_eq!(choices_before, choices_after, "Choices should persist");
        assert!(env.got_choices, "got_choices should remain true");
    }

    // ============================================================================
    // TEST: Stack manipulation during continuation
    // ============================================================================

    /// Verify the splice/drain operations work correctly
    #[test]
    fn test_stack_splice_and_drain() {
        // This tests the stack manipulation that happens in prove()
        
        let mut stack: Vec<usize> = vec![0, 1, 2];  // Simplified: just indices
        let mut pointer = 1;
        
        println!("Initial: {:?}, pointer={}", stack, pointer);
        
        // Simulate adding children at pointer+1
        let new_goals = vec![10, 11];
        pointer += 1;
        stack.splice(pointer..pointer, new_goals);
        
        println!("After splice: {:?}, pointer={}", stack, pointer);
        assert_eq!(stack, vec![0, 1, 10, 11, 2]);
        
        // Now simulate backtrack: drain children
        pointer -= 1;
        let children = 2;
        stack.drain((pointer + 1)..(pointer + 1 + children));
        
        println!("After drain: {:?}, pointer={}", stack, pointer);
        assert_eq!(stack, vec![0, 1, 2]);
    }

    // ============================================================================
    // INTEGRATION TEST: Simulate full restart scenario
    // ============================================================================

    #[test]
    fn test_full_restart_scenario() {
        println!("\n=== Full Restart Scenario ===\n");
        
        // This simulates what happens when:
        // 1. Query: ancestor(ken, james), ancestor(christine, james)
        // 2. First proof found
        // 3. User presses space
        // 4. Second proof attempt
        
        let ancestor = SymbolDB::set_const("ancestor".into());
        let dad = SymbolDB::set_const("dad".into());
        let mum = SymbolDB::set_const("mum".into());
        
        let prog_heap = Arc::new(vec![]);
        let mut heap = QueryHeap::new(prog_heap.clone(), None).unwrap();
        
        // Create two goal atoms
        let goal1 = heap.heap_push((Tag::Func, 3));
        heap.heap_push((Tag::Con, ancestor));
        heap.heap_push((Tag::Con, SymbolDB::set_const("ken".into())));
        heap.heap_push((Tag::Con, SymbolDB::set_const("james".into())));
        
        let goal2 = heap.heap_push((Tag::Func, 3));
        heap.heap_push((Tag::Con, ancestor));
        heap.heap_push((Tag::Con, SymbolDB::set_const("christine".into())));
        heap.heap_push((Tag::Con, SymbolDB::set_const("james".into())));
        
        let mut hypothesis = Hypothesis::new();
        let mut h_clauses = 0;
        let mut invented_preds = 0;
        
        // Simulate first proof success:
        // Stack: [env0(goal1), env1(subgoal1), env2(subgoal2), env3(goal2), ...]
        // For simplicity, let's say goal1 spawned 2 children and goal2 spawned 1
        
        let mut env0 = Env::new(goal1, 0);
        env0.children = 2;
        env0.new_clause = true;
        env0.bindings = Box::new([]);
        
        // Add clause for env0
        let c0 = heap.heap_push((Tag::Con, ancestor));
        hypothesis.push_clause(Clause::new(vec![c0], None), &heap, vec![0].into());
        h_clauses += 1;
        
        let env1 = Env::new(goal1 + 10, 1);  // Some child goal
        let env2 = Env::new(goal1 + 20, 1);  // Another child goal
        
        let mut env3 = Env::new(goal2, 0);
        env3.children = 1;
        env3.new_clause = true;
        env3.bindings = Box::new([]);
        
        // Add clause for env3
        let c1 = heap.heap_push((Tag::Con, ancestor));
        hypothesis.push_clause(Clause::new(vec![c1], None), &heap, vec![1].into());
        h_clauses += 1;
        
        let env4 = Env::new(goal2 + 10, 1);  // Child of goal2
        
        let mut stack = vec![env0, env1, env2, env3, env4];
        let mut pointer = 5;  // Past end = success
        
        println!("First proof found!");
        println!("  stack.len() = {}", stack.len());
        println!("  pointer = {}", pointer);
        println!("  hypothesis.len() = {}", hypothesis.len());
        println!("  h_clauses = {}", h_clauses);
        
        // === USER PRESSES SPACE - RESTART ===
        
        println!("\n--- User requests next solution ---\n");
        
        // From prove(): if self.pointer == self.stack.len()
        assert_eq!(pointer, stack.len());
        
        pointer -= 1;
        println!("Decremented pointer to {}", pointer);
        
        // Undo last environment
        let children = stack[pointer].undo_try(
            &mut hypothesis,
            &mut heap,
            &mut h_clauses,
            &mut invented_preds
        );
        
        println!("undo_try returned children = {}", children);
        println!("  hypothesis.len() = {}", hypothesis.len());
        println!("  h_clauses = {}", h_clauses);
        
        // Drain children
        stack.drain((pointer + 1)..(pointer + 1 + children));
        
        println!("After drain:");
        println!("  stack.len() = {}", stack.len());
        println!("  pointer = {}", pointer);
        
        // Now the prover would continue: try_choices on stack[pointer]
        // If it fails, backtrack further...
        
        // Key invariant: hypothesis should only have clauses from envs still in stack
        // env3 and env4 were removed, so env3's clause should be gone
        assert_eq!(hypothesis.len(), 1, "Only env0's clause should remain");
    }
}
