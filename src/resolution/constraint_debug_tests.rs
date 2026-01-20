/// Focused debugging tests for constraint validation in MIL
/// 
/// The constraint system prevents different meta-variables (predicate symbols
/// in meta-rules) from being unified to the same value during learning.
/// 
/// This file contains tests specifically designed to expose bugs in:
/// 1. The check_constraints implementation in Substitution
/// 2. Constraint collection when creating hypothesis clauses
/// 3. Constraint propagation through multiple hypothesis clauses

#[cfg(test)]
mod constraint_debug_tests {
    use std::sync::Arc;
    use crate::{
        heap::heap::{Cell, Heap, Tag},
        program::{
            clause::{BitFlag64, Clause},
            hypothesis::Hypothesis,
        },
        resolution::unification::Substitution,
        heap::symbol_db::SymbolDB,
    };

    // ============================================================================
    // BUG HUNT 1: check_constraints implementation
    // ============================================================================
    
    /// The current check_constraints logic:
    /// ```
    /// for binding in bindings {
    ///     if constraints.contains(&heap.deref_addr(binding.0)) 
    ///        && constraints.contains(&heap.deref_addr(binding.1)) {
    ///         return false;
    ///     }
    /// }
    /// ```
    /// 
    /// POTENTIAL BUG: This checks if BOTH sides of a SINGLE binding are in constraints.
    /// But the actual constraint violation is when TWO DIFFERENT bindings 
    /// have their TARGET addresses equal (both pointing to same predicate).
    /// 
    /// This test exposes this potential bug.
    #[test]
    fn test_constraint_logic_bug_same_target() {
        let p = SymbolDB::set_const("p".into());
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Meta-var P
            (Tag::Ref, 1),      // 1: Meta-var Q
            (Tag::Con, p),      // 2: Predicate constant 'p'
        ];
        
        // Constraints say: addresses 0 and 1 (the meta-vars) can't unify to same value
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        let mut sub = Substitution::default();
        // CRITICAL: Both meta-vars bound to the SAME target address (2 = 'p')
        sub = sub.push((0, 2, false));  // P -> 'p'
        sub = sub.push((1, 2, false));  // Q -> 'p' (SAME!)
        
        // Expected: This SHOULD fail because P and Q both resolve to 'p'
        // 
        // Current logic checks each binding individually:
        //   - binding (0, 2): Is deref(0)=0 in constraints? YES. Is deref(2)=2 in constraints? NO.
        //   - binding (1, 2): Is deref(1)=1 in constraints? YES. Is deref(2)=2 in constraints? NO.
        // Current result: PASSES (WRONG!)
        //
        // Correct logic should check: Are any two constrained vars bound to the same target?
        //   - deref of binding targets: binding 0 target = 2, binding 1 target = 2
        //   - Are 0 and 1 both in constraints AND both bound to same target? YES
        // Correct result: FAILS
        
        let result = sub.check_constraints(&constraints, &heap);
        
        // If this assertion fails, the bug is confirmed
        assert!(
            !result,
            "BUG DETECTED: check_constraints should fail when two meta-vars bound to same target. \
             P (addr 0) and Q (addr 1) are both bound to 'p' (addr 2)"
        );
    }

    /// Alternative test: What the current implementation ACTUALLY checks
    #[test]
    fn test_what_current_impl_checks() {
        let p = SymbolDB::set_const("p".into());
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Constrained
            (Tag::Ref, 1),      // 1: Constrained
            (Tag::Con, p),      // 2
        ];
        
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        // The current implementation would only fail if BOTH SIDES of a SINGLE binding
        // are in the constraints list. Let's create that scenario:
        let mut sub = Substitution::default();
        sub = sub.push((0, 1, false));  // Binding: 0 -> 1 (both are in constraints!)
        
        let result = sub.check_constraints(&constraints, &heap);
        
        // This SHOULD fail and probably DOES fail with current impl
        println!("Binding (0->1) where both 0,1 are constrained: passes={}", result);
    }

    // ============================================================================
    // BUG HUNT 2: Constraint addresses might be stale after heap grows
    // ============================================================================

    /// When a meta-clause is matched, new terms are built on the heap.
    /// If constraints store heap addresses but those addresses aren't updated
    /// when terms are rebuilt, the constraints become stale.
    #[test]
    fn test_constraint_address_staleness() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        
        let mut heap: Vec<Cell> = vec![
            (Tag::Arg, 0),      // 0: Original Arg0
            (Tag::Arg, 1),      // 1: Original Arg1
            (Tag::Con, p),      // 2: 'p'
            (Tag::Con, q),      // 3: 'q'
        ];
        
        // Initial constraints reference addresses 0 and 1
        let constraints: Arc<[usize]> = vec![0, 1].into();
        
        // Simulate building new terms (as build() does)
        // This creates NEW refs at different addresses
        let new_ref_0 = heap.set_ref(Some(2));  // Ref pointing to 'p' at addr 4
        let new_ref_1 = heap.set_ref(Some(2));  // Ref pointing to 'p' at addr 5 (same target!)
        
        println!("Original constraint addresses: {:?}", &*constraints);
        println!("New ref addresses: {} -> 2, {} -> 2", new_ref_0, new_ref_1);
        
        // Now substitution uses the NEW addresses
        let mut sub = Substitution::default();
        sub = sub.push((new_ref_0, 2, false));
        sub = sub.push((new_ref_1, 2, false));
        
        // The constraint check uses the OLD addresses (0, 1)
        // but bindings use NEW addresses (4, 5)
        // This means the constraint check might not catch the violation!
        
        let result = sub.check_constraints(&constraints, &heap);
        
        println!("Staleness test: constraints={:?}, bindings at ({}, {}), result={}",
                 &*constraints, new_ref_0, new_ref_1, result);
        
        // Note: This might PASS incorrectly because constraints reference 0,1
        // but bindings reference 4,5
    }

    // ============================================================================
    // BUG HUNT 3: Constraint collection might use wrong addresses
    // ============================================================================

    /// In proof.rs, constraints are collected like this:
    /// ```
    /// for i in 0..32 {
    ///     if clause.meta_var(i).unwrap_unchecked() {
    ///         constraints.push(substitution.get_arg(i).unwrap_unchecked());
    ///     }
    /// }
    /// ```
    /// 
    /// This collects the ADDRESS that each meta-var is bound to.
    /// But check_constraints checks if BINDING SOURCES are in constraints.
    /// 
    /// This test explores the mismatch.
    #[test]
    fn test_constraint_source_vs_target_confusion() {
        let p = SymbolDB::set_const("p".into());
        
        let heap: Vec<Cell> = vec![
            (Tag::Arg, 0),      // 0: Meta-var P (Arg0)
            (Tag::Arg, 1),      // 1: Meta-var Q (Arg1)
            (Tag::Ref, 2),      // 2: Query ref for P
            (Tag::Ref, 3),      // 3: Query ref for Q
            (Tag::Con, p),      // 4: 'p'
        ];
        
        // During try_choices, after unification + building:
        let mut sub = Substitution::default();
        sub.set_arg(0, 4);  // Arg0 (P) -> address 4 ('p')
        sub.set_arg(1, 4);  // Arg1 (Q) -> address 4 ('p') -- SAME!
        
        // Constraint collection (as in proof.rs):
        // constraints = [sub.get_arg(0), sub.get_arg(1)] = [4, 4]
        let constraints: Arc<[usize]> = vec![
            sub.get_arg(0).unwrap(),  // 4
            sub.get_arg(1).unwrap(),  // 4
        ].into();
        
        println!("Collected constraints: {:?}", &*constraints);
        
        // Later, when checking a NEW substitution against these constraints:
        let mut new_sub = Substitution::default();
        new_sub = new_sub.push((2, 4, false));  // Some ref bound to 4
        new_sub = new_sub.push((3, 4, false));  // Another ref bound to 4
        
        // check_constraints checks: deref(2) in constraints? deref(4) in constraints?
        // deref(2) = 2 (if Ref 2 is unbound) -> not in [4,4]
        // deref(4) = 4 (Con) -> IS in [4,4]
        
        // For binding (2, 4): deref(2)=2 not in [4,4], deref(4)=4 in [4,4] -> passes
        // For binding (3, 4): deref(3)=3 not in [4,4], deref(4)=4 in [4,4] -> passes
        
        let result = new_sub.check_constraints(&constraints, &heap);
        println!("Source vs target test: result={}", result);
        
        // This shows that if constraints contain TARGETS (predicate addresses)
        // rather than SOURCES (meta-var addresses), the logic is different.
    }

    // ============================================================================
    // PROPOSED FIX: Alternative constraint check implementation
    // ============================================================================

    /// This test demonstrates what the correct constraint logic SHOULD be
    #[test]
    fn test_correct_constraint_logic() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),      // 0: Meta-var ref
            (Tag::Ref, 1),      // 1: Meta-var ref
            (Tag::Con, p),      // 2: 'p'
            (Tag::Con, q),      // 3: 'q'
        ];
        
        // Constraints: addresses 0 and 1 are meta-var positions
        let constraints: &[usize] = &[0, 1];
        
        let mut sub = Substitution::default();
        sub = sub.push((0, 2, false));  // 0 -> 2 ('p')
        sub = sub.push((1, 2, false));  // 1 -> 2 ('p') -- SAME TARGET
        
        // CORRECT LOGIC:
        // For each pair of constrained addresses, check if they're bound to same target
        fn correct_check_constraints(
            sub: &Substitution,
            constraints: &[usize],
            heap: &impl Heap
        ) -> bool {
            // Collect final targets for each constrained address
            let mut targets: Vec<(usize, usize)> = Vec::new();  // (constraint_addr, final_target)
            
            for &constraint_addr in constraints {
                // Find what this constraint address is bound to
                if let Some(target) = sub.bound(constraint_addr) {
                    let final_target = heap.deref_addr(target);
                    targets.push((constraint_addr, final_target));
                }
            }
            
            // Check if any two constrained addresses have the same final target
            for i in 0..targets.len() {
                for j in (i+1)..targets.len() {
                    if targets[i].1 == targets[j].1 {
                        println!(
                            "Constraint violation: {} and {} both bound to {}",
                            targets[i].0, targets[j].0, targets[i].1
                        );
                        return false;
                    }
                }
            }
            true
        }
        
        let result = correct_check_constraints(&sub, constraints, &heap);
        assert!(!result, "Correct logic should detect the violation");
        
        // Now test with different targets
        let mut sub2 = Substitution::default();
        sub2 = sub2.push((0, 2, false));  // 0 -> 2 ('p')
        sub2 = sub2.push((1, 3, false));  // 1 -> 3 ('q') -- DIFFERENT
        
        let result2 = correct_check_constraints(&sub2, constraints, &heap);
        assert!(result2, "Correct logic should allow different targets");
    }

    // ============================================================================
    // BUG HUNT 4: Multiple hypothesis constraints interaction
    // ============================================================================

    /// When multiple clauses are in the hypothesis, EACH has its own constraints.
    /// A new substitution must satisfy ALL of them.
    #[test]
    fn test_multiple_hypothesis_constraints() {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());
        let r = SymbolDB::set_const("r".into());
        
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Con, p),  // 3
            (Tag::Con, q),  // 4
            (Tag::Con, r),  // 5
        ];
        
        let mut hypothesis = Hypothesis::new();
        
        // Clause 1: constraints on [0, 1]
        let c1 = Clause::new(vec![], None);
        hypothesis.push_clause(c1, &heap, vec![0, 1].into());
        
        // Clause 2: constraints on [1, 2]
        let c2 = Clause::new(vec![], None);
        hypothesis.push_clause(c2, &heap, vec![1, 2].into());
        
        // Now a substitution must satisfy BOTH constraint sets
        let mut sub = Substitution::default();
        sub = sub.push((0, 3, false));  // 0 -> p
        sub = sub.push((1, 4, false));  // 1 -> q
        sub = sub.push((2, 4, false));  // 2 -> q  (violates constraint [1,2]!)
        
        // Check against EACH constraint set
        let mut all_passed = true;
        for constraint in &hypothesis.constraints {
            if !sub.check_constraints(constraint, &heap) {
                all_passed = false;
                println!("Failed constraint: {:?}", &**constraint);
            }
        }
        
        // With current logic, this might incorrectly pass
        // because each individual check uses the buggy logic
        println!("Multiple constraints result: all_passed={}", all_passed);
    }

    // ============================================================================
    // INTEGRATION TEST: Full retry scenario
    // ============================================================================

    /// Simulate a retry scenario where constraints from a removed clause
    /// should no longer be checked
    #[test]
    fn test_retry_clears_constraints() {
        let heap: Vec<Cell> = vec![
            (Tag::Ref, 0),
        ];
        
        let mut hypothesis = Hypothesis::new();
        
        // Add clause with constraints
        let c1 = Clause::new(vec![], None);
        hypothesis.push_clause(c1, &heap, vec![0].into());
        
        assert_eq!(hypothesis.constraints.len(), 1);
        
        // Simulate retry: pop the clause
        hypothesis.pop_clause();
        
        assert_eq!(hypothesis.len(), 0);
        assert_eq!(
            hypothesis.constraints.len(), 
            0, 
            "Constraints should be removed when clause is popped"
        );
        
        // Now add a different clause
        let c2 = Clause::new(vec![], None);
        hypothesis.push_clause(c2, &heap, vec![].into());  // No constraints
        
        assert_eq!(hypothesis.constraints.len(), 1);
        assert_eq!(
            hypothesis.constraints[0].len(),
            0,
            "New clause should have empty constraints, not old ones"
        );
    }
}
