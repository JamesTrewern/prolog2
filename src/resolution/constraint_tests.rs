// Test suite for diagnosing constraint behaviour in Meta-Interpretive Learning
//
// The constraint system is supposed to prevent different existentially quantified
// variables in metarules from being bound to the same predicate symbol.
// For example, in P(A):-Q(A),R(A),{P,Q,R}, if P=Q=R=e then we get the
// tautological clause e(A):-e(A),e(A) which causes infinite loops.
//
// This test suite probes:
// 1. Basic check_constraints behaviour on substitutions
// 2. Constraint creation from metarule matching
// 3. Whether constraints from clause N prevent bad bindings in clause N+1
// 4. Whether constraints prevent bad bindings within the SAME clause (the trains bug)
// 5. End-to-end proof scenarios that should/shouldn't be blocked

use crate::{
    heap::{
        heap::{Cell, Heap, Tag},
        symbol_db::SymbolDB,
    },
    parser::{
        build_tree::TokenStream,
        execute_tree::execute_tree,
        tokeniser::tokenise,
    },
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_table::PredicateTable,
    },
    resolution::{
        build::build,
        unification::{unify, Substitution},
    },
};

// =============================================================================
// Group 1: Basic check_constraints behaviour
// =============================================================================

/// Two constraint addresses pointing to different constants should PASS
#[test]
fn constraints_different_constants_pass() {
    let a = SymbolDB::set_const("a".into());
    let b = SymbolDB::set_const("b".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, a),  // 0: constant 'a'
        (Tag::Con, b),  // 1: constant 'b'
    ];

    let constraints: Vec<usize> = vec![0, 1];
    let sub = Substitution::default();
    assert!(
        sub.check_constraints(&constraints, &heap),
        "Different constants should pass constraint check"
    );
}

/// Two constraint addresses pointing to the SAME constant should FAIL
#[test]
fn constraints_same_constant_fail() {
    let a = SymbolDB::set_const("ca".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, a),  // 0: constant 'a'
        (Tag::Con, a),  // 1: also constant 'a'
    ];

    let constraints: Vec<usize> = vec![0, 1];
    let sub = Substitution::default();
    // Two different addresses with the same constant value
    // check_constraints checks if addresses resolve to the SAME TARGET
    // Since 0 and 1 are different addresses (both Con), they won't deref to each other
    let result = sub.check_constraints(&constraints, &heap);
    println!("Same constant at different addresses: {}", result);
    // This documents current behaviour - they are at different addresses so they
    // may or may not be detected as "same" depending on implementation
}

/// Two constraint addresses where both refs point to same target should FAIL
#[test]
fn constraints_refs_to_same_target_fail() {
    let a = SymbolDB::set_const("cref".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, a),  // 0: constant 'a'
        (Tag::Ref, 0),  // 1: ref -> 0 (points to 'a')
        (Tag::Ref, 0),  // 2: ref -> 0 (also points to 'a')
    ];

    let constraints: Vec<usize> = vec![1, 2];
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    assert!(
        !result,
        "Two refs pointing to same target should FAIL constraint check, got: {}",
        result
    );
}

/// Three constraint addresses, two same and one different
#[test]
fn constraints_three_vars_two_same() {
    let a = SymbolDB::set_const("c3a".into());
    let b = SymbolDB::set_const("c3b".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, a),  // 0
        (Tag::Con, b),  // 1
        (Tag::Ref, 0),  // 2: ref -> 0 (same as addr 0 = 'a')
    ];

    let constraints: Vec<usize> = vec![0, 1, 2];
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    // constraint_addr 0 and constraint_addr 2 both resolve to address 0
    assert!(
        !result,
        "Three constraints where two resolve to same target should FAIL, got: {}",
        result
    );
}

/// Constraint with pending substitution bindings
#[test]
fn constraints_with_substitution_bindings() {
    let a = SymbolDB::set_const("csb_a".into());

    let heap: Vec<Cell> = vec![
        (Tag::Ref, 0),  // 0: unbound ref
        (Tag::Ref, 1),  // 1: unbound ref
        (Tag::Con, a),  // 2: constant 'a'
    ];

    // Substitution binds both ref 0 and ref 1 to constant 'a' at addr 2
    let sub = Substitution::default()
        .push((0, 2, false))
        .push((1, 2, false));

    let constraints: Vec<usize> = vec![0, 1];
    let result = sub.check_constraints(&constraints, &heap);
    assert!(
        !result,
        "Two refs both bound (via substitution) to same target should FAIL, got: {}",
        result
    );
}

/// Constraint where substitution bindings go to different targets
#[test]
fn constraints_with_different_substitution_bindings_pass() {
    let a = SymbolDB::set_const("csdb_a".into());
    let b = SymbolDB::set_const("csdb_b".into());

    let heap: Vec<Cell> = vec![
        (Tag::Ref, 0),  // 0: unbound ref
        (Tag::Ref, 1),  // 1: unbound ref
        (Tag::Con, a),  // 2: constant 'a'
        (Tag::Con, b),  // 3: constant 'b'
    ];

    let sub = Substitution::default()
        .push((0, 2, false))
        .push((1, 3, false));

    let constraints: Vec<usize> = vec![0, 1];
    let result = sub.check_constraints(&constraints, &heap);
    assert!(
        result,
        "Two refs bound to different targets should PASS, got: {}",
        result
    );
}

// =============================================================================
// Group 2: Constraint addresses come from Arg registers after metarule matching
// These test what addresses actually get stored as constraints
// =============================================================================

/// Simulate matching metarule P(A):-Q(A),{P,Q} where P and Q are meta_vars
/// When P=e and Q=short, constraints should store the addresses that P and Q resolved to
#[test]
fn constraint_creation_from_metarule_match() {
    let e_sym = SymbolDB::set_const("cc_e".into());
    let _short_sym = SymbolDB::set_const("cc_short".into());

    // Metarule: P(A):-Q(A),{P,Q}
    // Encoded as: Func(2), Arg(0), Arg(1) | Func(2), Arg(2), Arg(1)
    // meta_vars = {0, 2} (P and Q are meta_vars; A=arg(1) is universally quantified)
    let mut heap: Vec<Cell> = vec![
        // Metarule head: P(A) = Func(2), Arg(0), Arg(1)
        (Tag::Func, 2), // 0
        (Tag::Arg, 0),  // 1: P
        (Tag::Arg, 1),  // 2: A
        // Metarule body: Q(A) = Func(2), Arg(2), Arg(1)
        (Tag::Func, 2), // 3
        (Tag::Arg, 2),  // 4: Q
        (Tag::Arg, 1),  // 5: A (same arg as head)
        // Goal: e(X) where X is unbound
        (Tag::Func, 2), // 6
        (Tag::Con, e_sym), // 7: e
        (Tag::Ref, 8),  // 8: X (unbound)
    ];

    // Unify metarule head (addr 0) with goal (addr 6)
    let sub = unify(&heap, 0, 6).unwrap();

    // Arg 0 (P) should be bound to addr 7 (Con e)
    assert_eq!(sub.get_arg(0), Some(7), "P should be bound to 'e' address");
    // Arg 1 (A) should be bound to addr 8 (Ref X)
    assert_eq!(sub.get_arg(1), Some(8), "A should be bound to X ref");
    // Arg 2 (Q) should be unbound (no match yet)
    assert_eq!(sub.get_arg(2), None, "Q should not yet be bound");

    println!("After matching P(A) with e(X):");
    println!("  Arg 0 (P) -> {:?}", sub.get_arg(0));
    println!("  Arg 1 (A) -> {:?}", sub.get_arg(1));
    println!("  Arg 2 (Q) -> {:?}", sub.get_arg(2));

    // Now simulate what happens when building the hypothesis clause:
    // constraints collect addresses for each meta_var arg
    // meta_vars are {0, 2} (P and Q)
    // Arg 0 has address 7 (Con e)
    // Arg 2 is still None!
    // This means the constraint for Q is missing at clause creation time
    // because Q hasn't been resolved yet - it gets resolved when proving body goals

    println!("\nKey finding: At constraint creation time, body predicate vars may be unbound!");
    println!("Arg 0 (P) bound: {}", sub.get_arg(0).is_some());
    println!("Arg 2 (Q) bound: {}", sub.get_arg(2).is_some());
}

// =============================================================================
// Group 3: The trains bug scenario
// Metarule: P(A):-Q(A),R(A),{P,Q,R}
// If P=e, Q=e, R=e we get e(A):-e(A),e(A)
// =============================================================================

/// Simulate the exact trains scenario: P(A):-Q(A),R(A),{P,Q,R} matching e(east1)
#[test]
fn trains_bug_metarule_self_reference() {
    let e_sym = SymbolDB::set_const("tb_e".into());

    // Metarule: P(A):-Q(A),R(A),{P,Q,R}
    let heap: Vec<Cell> = vec![
        // Head: P(A) = Func(2), Arg(0=P), Arg(1=A)
        (Tag::Func, 2), // 0
        (Tag::Arg, 0),  // 1: P
        (Tag::Arg, 1),  // 2: A
        // Body1: Q(A) = Func(2), Arg(2=Q), Arg(1=A)
        (Tag::Func, 2), // 3
        (Tag::Arg, 2),  // 4: Q
        (Tag::Arg, 1),  // 5: A
        // Body2: R(A) = Func(2), Arg(3=R), Arg(1=A)
        (Tag::Func, 2), // 6
        (Tag::Arg, 3),  // 7: R
        (Tag::Arg, 1),  // 8: A
        // Goal: e(east1) - but for constraint testing we just need e(X)
        (Tag::Func, 2),    // 9
        (Tag::Con, e_sym), // 10: e
        (Tag::Ref, 11),    // 11: unbound ref
    ];

    // Unify head P(A) at addr 0 with goal e(X) at addr 9
    let sub = unify(&heap, 0, 9).unwrap();

    println!("After unifying P(A) with e(X):");
    println!("  Arg 0 (P) -> {:?} = e", sub.get_arg(0));
    println!("  Arg 1 (A) -> {:?} = X", sub.get_arg(1));
    println!("  Arg 2 (Q) -> {:?} = unbound", sub.get_arg(2));
    println!("  Arg 3 (R) -> {:?} = unbound", sub.get_arg(3));

    // At this point, only P is bound (to e). Q and R are unbound.
    // The constraint system builds constraints from meta_vars {P=0, Q=2, R=3}:
    //   constraints = [sub.get_arg(0), sub.get_arg(2), sub.get_arg(3)]
    //   = [Some(10), None, None]  (addr 10 is Con e)
    //
    // But the code does: `unsafe { substitution.get_arg(i).unwrap_unchecked() }`
    // which on None gives garbage/0/undefined behaviour!

    let arg0 = sub.get_arg(0);
    let arg2 = sub.get_arg(2);
    let arg3 = sub.get_arg(3);

    println!("\nConstraint creation attempt:");
    println!("  meta_var 0 (P): {:?}", arg0);
    println!("  meta_var 2 (Q): {:?}", arg2);
    println!("  meta_var 3 (R): {:?}", arg3);

    // KEY FINDING: Q and R are None at constraint creation time!
    // The unsafe unwrap_unchecked on None is undefined behaviour.
    assert!(
        arg2.is_none(),
        "Q should be unbound at constraint creation - this is the root of the bug"
    );
    assert!(
        arg3.is_none(),
        "R should be unbound at constraint creation - this is the root of the bug"
    );
}

/// Test what check_constraints does when constraint addresses are 0 (from unwrap_unchecked on None)
#[test]
fn constraints_with_garbage_zero_addresses() {
    let a_sym = SymbolDB::set_const("cg_a".into());
    let b_sym = SymbolDB::set_const("cg_b".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, a_sym), // 0: constant 'a'
        (Tag::Con, b_sym), // 1: constant 'b'
    ];

    // If unwrap_unchecked on None gives 0, then constraints would be [addr_of_P, 0, 0]
    // where 0 happens to be the first cell on the heap
    let constraints: Vec<usize> = vec![0, 0, 0];
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    println!(
        "Constraints with three 0 addresses: {} (should be false since all same)",
        result
    );
    // With all constraints pointing to addr 0, constraint_addr[0]=0 and constraint_addr[1]=0
    // are different indices with same target, so should fail
    // BUT: the check says `constrained_targets[i].0 != constrained_targets[j].0`
    // Here constrained_targets[i].0 is the ORIGINAL constraint address, which is also 0 for all
    // So constraint_addr 0 == constraint_addr 0, meaning the check doesn't detect duplicates
    // when the constraint addresses themselves are identical!
    println!(
        "Note: check_constraints skips pairs where original addresses are equal"
    );
}

// =============================================================================
// Group 4: Full integration - parse metarule, match, build clause, check constraints
// =============================================================================

/// Parse the actual metarule P(A):-Q(A),R(A),{P,Q,R} and examine its structure
#[test]
fn parse_trains_metarule_structure() {
    let mut heap = Vec::<Cell>::new();
    let mut pred_table = PredicateTable::new();

    let tree = TokenStream::new(
        tokenise("P(A):-Q(A),R(A),{P,Q,R}.".into()).unwrap()
    ).parse_all().unwrap();

    execute_tree(tree, &mut heap, &mut pred_table);

    // This metarule has a variable predicate symbol, so it should be in variable clauses
    // The head has arity 1 (P is the predicate, A is the arg)
    // Let's find it - variable clauses are stored by arity
    if let Some(clauses) = pred_table.get_variable_clauses(1) {
        assert!(!clauses.is_empty(), "Should have at least one variable clause for arity 1");
        let clause = &clauses[0];

        println!("Parsed metarule clause:");
        println!("  Head addr: {}", clause.head());
        println!("  Body addrs: {:?}", clause.body());
        println!("  Is meta: {}", clause.meta());
        println!("  Full: {}", clause.to_string(&heap));

        // Check meta_vars
        for i in 0..8 {
            if let Ok(is_meta) = clause.meta_var(i) {
                if is_meta {
                    println!("  Arg {} is a meta_var", i);
                }
            }
        }

        // Examine heap cells for each literal
        println!("\nHead literal cells:");
        let h = clause.head();
        for offset in 0..3 {
            println!("  [{}]: {:?}", h + offset, heap[h + offset]);
        }

        println!("Body literal 1 cells:");
        let b1 = clause.body()[0];
        for offset in 0..3 {
            println!("  [{}]: {:?}", b1 + offset, heap[b1 + offset]);
        }

        println!("Body literal 2 cells:");
        let b2 = clause.body()[1];
        for offset in 0..3 {
            println!("  [{}]: {:?}", b2 + offset, heap[b2 + offset]);
        }
    } else {
        panic!("No variable clauses found for arity 1");
    }
}

/// Parse P(A):-Q(A),{P,Q} and verify which args are meta_vars
#[test]
fn parse_simple_metarule_meta_vars() {
    let mut heap = Vec::<Cell>::new();
    let mut pred_table = PredicateTable::new();

    let tree = TokenStream::new(
        tokenise("P(A):-Q(A),{P,Q}.".into()).unwrap()
    ).parse_all().unwrap();

    execute_tree(tree, &mut heap, &mut pred_table);

    if let Some(clauses) = pred_table.get_variable_clauses(1) {
        let clause = &clauses[0];
        println!("Metarule P(A):-Q(A),{{P,Q}}:");
        println!("  Full: {}", clause.to_string(&heap));

        // Find which arg indices correspond to P, Q, A
        // In the parser, variables get assigned arg indices in order of first appearance
        // P appears first (in head), then A, then Q (in body)
        // So: P=Arg(0), A=Arg(1), Q=Arg(2)

        let mut meta_var_indices: Vec<usize> = Vec::new();
        let mut non_meta_var_indices: Vec<usize> = Vec::new();
        for i in 0..8 {
            if let Ok(is_meta) = clause.meta_var(i) {
                if is_meta {
                    meta_var_indices.push(i);
                } else {
                    // Only count args that actually appear in the clause
                }
            }
        }
        println!("  Meta var arg indices: {:?}", meta_var_indices);

        // The meta_vars set {P,Q} should mark P and Q as meta_vars
        // P=Arg(0), Q=Arg(2) should be meta_vars
        // A=Arg(1) should NOT be a meta_var
        assert!(clause.meta_var(0).unwrap_or(false), "P (Arg 0) should be meta_var");
        println!("  Arg 0 (P) is meta_var: {}", clause.meta_var(0).unwrap_or(false));
        println!("  Arg 1 (A) is meta_var: {}", clause.meta_var(1).unwrap_or(false));
        println!("  Arg 2 (Q) is meta_var: {}", clause.meta_var(2).unwrap_or(false));
    }
}

// =============================================================================
// Group 5: End-to-end constraint scenarios
// =============================================================================

/// Test that when hypothesis has clause with constraints [addr_P, addr_Q],
/// a NEW metarule match that would bind to the same targets is rejected
#[test]
fn cross_clause_constraint_check() {
    let e_sym = SymbolDB::set_const("ccc_e".into());
    let short_sym = SymbolDB::set_const("ccc_short".into());
    let closed_sym = SymbolDB::set_const("ccc_closed".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),     // 0: e
        (Tag::Con, short_sym), // 1: short
        (Tag::Con, closed_sym),// 2: closed
        // Refs for a new substitution
        (Tag::Ref, 3),        // 3: unbound ref (will be bound to P target)
        (Tag::Ref, 4),        // 4: unbound ref (will be bound to Q target)
    ];

    // Simulate a previous hypothesis clause having constraints [0, 1]
    // (P was bound to addr 0 = 'e', Q was bound to addr 1 = 'short')
    let existing_constraints: Vec<usize> = vec![0, 1];

    // New substitution that would bind ref 3 -> 0 (e) and ref 4 -> 1 (short)
    let sub = Substitution::default()
        .push((3, 0, false))   // new P -> e
        .push((4, 1, false));  // new Q -> short

    // This should PASS because the existing constraints [0,1] are about
    // the previous clause's bindings. The check sees if the new substitution
    // causes addresses 0 and 1 to resolve to the same target.
    // addr 0 = Con e (no pending binding), addr 1 = Con short (no pending binding)
    // They're different, so it passes.
    let result = sub.check_constraints(&existing_constraints, &heap);
    println!("Cross-clause check (different targets): {}", result);
    assert!(result, "Different existing constraint targets should pass");

    // Now test: existing constraints where both point to refs that the
    // new substitution binds to the same target
    let heap2: Vec<Cell> = vec![
        (Tag::Ref, 0),  // 0: ref to self (unbound, was bound to e in prev clause)
        (Tag::Ref, 1),  // 1: ref to self (unbound, was bound to short in prev clause)
        (Tag::Con, e_sym), // 2: e
    ];

    // But after the previous clause was undone (backtracking), these refs are unbound again
    // New substitution binds both to 'e'
    let sub2 = Substitution::default()
        .push((0, 2, false))
        .push((1, 2, false));

    let result2 = sub2.check_constraints(&existing_constraints, &heap2);
    println!("Cross-clause check (same target via sub): {}", result2);
    // Both constraint addresses 0 and 1 now resolve (via sub) to addr 2
    assert!(!result2, "Two constraints resolving to same target should FAIL");
}

/// Test the actual constraint flow: constraints are checked for each EXISTING
/// hypothesis constraint against the CURRENT substitution. New clause constraints
/// are added AFTER the check. So there's no self-check.
#[test]
fn no_self_constraint_check() {
    // This test documents the architectural issue:
    // When clause C is being created, its constraints haven't been added yet,
    // so check_constraints only checks against PREVIOUS clauses' constraints.
    //
    // If clause C is the FIRST hypothesis clause, there are NO constraints to check against!

    let hypothesis = Hypothesis::new();
    assert_eq!(
        hypothesis.constraints.len(),
        0,
        "Empty hypothesis has no constraints"
    );

    // Therefore, the FIRST metarule match NEVER has its substitution checked
    // against any constraints. P=Q=R=e would pass because there's nothing to check.
    println!("Empty hypothesis means first clause has NO constraint checks!");
    println!("This is why e(A):-e(A),e(A) can be generated as the first hypothesis clause.");
}

/// Demonstrate that constraints only accumulate - they don't protect the first clause
#[test]
fn first_clause_unprotected() {
    let e_sym = SymbolDB::set_const("fcu_e".into());

    let heap: Vec<Cell> = vec![
        (Tag::Ref, 0),        // 0: will be P
        (Tag::Ref, 1),        // 1: will be Q
        (Tag::Ref, 2),        // 2: will be R
        (Tag::Con, e_sym),    // 3: e
    ];

    // Substitution binding P=Q=R=e
    let sub = Substitution::default()
        .push((0, 3, false))   // P -> e
        .push((1, 3, false))   // Q -> e
        .push((2, 3, false));  // R -> e

    // With empty hypothesis, check_constraints is never called (loop over empty vec)
    let hypothesis = Hypothesis::new();
    let mut any_failed = false;
    for constraints in &hypothesis.constraints {
        if !sub.check_constraints(constraints, &heap) {
            any_failed = true;
        }
    }
    assert!(
        !any_failed,
        "With empty hypothesis, no constraints are checked, so P=Q=R=e is allowed"
    );
    println!("Confirmed: First hypothesis clause is completely unprotected by constraints");
}

// =============================================================================
// Group 6: What SHOULD happen - the fix we need
// =============================================================================

/// Demonstrate what a "self-constraint" check would look like
#[test]
fn proposed_self_constraint_check() {
    let e_sym = SymbolDB::set_const("psc_e".into());
    let short_sym = SymbolDB::set_const("psc_short".into());
    let closed_sym = SymbolDB::set_const("psc_closed".into());

    let heap: Vec<Cell> = vec![
        (Tag::Ref, 0),        // 0: P
        (Tag::Ref, 1),        // 1: Q
        (Tag::Ref, 2),        // 2: R
        (Tag::Con, e_sym),    // 3: e
        (Tag::Con, short_sym),// 4: short
        (Tag::Con, closed_sym),// 5: closed
    ];

    // GOOD case: P=e, Q=short, R=closed
    let good_sub = Substitution::default()
        .push((0, 3, false))
        .push((1, 4, false))
        .push((2, 5, false));

    // Constraints for the clause being created: [addr_P=0, addr_Q=1, addr_R=2]
    let self_constraints: Vec<usize> = vec![0, 1, 2];

    let good_result = good_sub.check_constraints(&self_constraints, &heap);
    assert!(good_result, "P=e, Q=short, R=closed should pass self-check");

    // BAD case: P=Q=R=e
    let bad_sub = Substitution::default()
        .push((0, 3, false))
        .push((1, 3, false))
        .push((2, 3, false));

    let bad_result = bad_sub.check_constraints(&self_constraints, &heap);
    assert!(
        !bad_result,
        "P=Q=R=e should FAIL self-check, got: {}",
        bad_result
    );
    println!("Self-constraint check correctly rejects P=Q=R=e: {}", !bad_result);

    // PARTIAL bad case: P=e, Q=e, R=closed
    let partial_bad_sub = Substitution::default()
        .push((0, 3, false))
        .push((1, 3, false))
        .push((2, 5, false));

    let partial_result = partial_bad_sub.check_constraints(&self_constraints, &heap);
    assert!(
        !partial_result,
        "P=e, Q=e, R=closed should FAIL self-check (P=Q), got: {}",
        partial_result
    );
}

/// Document the unsafe unwrap_unchecked issue with unset arg registers
#[test]
fn unsafe_unwrap_on_unset_args() {
    let sub = Substitution::default();

    // Arg 0 is not set
    let arg0 = sub.get_arg(0);
    assert_eq!(arg0, None, "Unset arg should return None");

    // In the actual code, `unsafe { substitution.get_arg(i).unwrap_unchecked() }`
    // on None is UB. In practice it often returns 0, but this is not guaranteed.
    // This means constraints built from unset args contain garbage addresses.
    println!("get_arg on unset returns: {:?}", arg0);
    println!("unsafe unwrap_unchecked on None is undefined behaviour!");
    println!("This means constraints may contain addr 0 or random values");
}

// =============================================================================
// Group 7: Same-symbol-different-address bypass
// =============================================================================

/// CRITICAL TEST: Two Con cells with the same symbol value but at different
/// heap addresses. check_constraints compares addresses, not symbol values.
/// If P's constraint points to Con(e) at addr 0, and Q's ref gets bound to
/// a DIFFERENT Con(e) at addr 5, the addresses differ and the check passes
/// even though they represent the same predicate.
#[test]
fn same_symbol_different_address_bypasses_constraint() {
    let e_sym = SymbolDB::set_const("bypass_e".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),  // 0: 'e' — P's constraint target
        (Tag::Ref, 1),      // 1: Q ref (unbound)
        (Tag::Ref, 2),      // 2: R ref (unbound)
        // ... later in the heap, another occurrence of 'e' from building a goal
        (Tag::Func, 2),     // 3: some goal structure
        (Tag::Con, e_sym),  // 4: ANOTHER 'e' constant cell — same symbol, different addr
        (Tag::Con, e_sym),  // 5: yet another 'e'
    ];

    // Constraints: P -> addr 0 (Con e), Q -> addr 1 (Ref), R -> addr 2 (Ref)
    let constraints: Vec<usize> = vec![0, 1, 2];

    // Simulate Q's ref being bound to the DIFFERENT 'e' cell at addr 4
    // and R's ref bound to yet another 'e' at addr 5
    let mut heap_mut = heap.clone();
    heap_mut[1] = (Tag::Ref, 4);  // Q ref -> addr 4 (Con e)
    heap_mut[2] = (Tag::Ref, 5);  // R ref -> addr 5 (Con e)

    let sub = Substitution::default();

    // P derefs to addr 0, Q derefs to addr 4, R derefs to addr 5
    // All three are Con(e_sym) but at DIFFERENT addresses
    println!("P constraint addr 0 deref -> {}", heap_mut.deref_addr(0));
    println!("Q constraint addr 1 deref -> {}", heap_mut.deref_addr(1));
    println!("R constraint addr 2 deref -> {}", heap_mut.deref_addr(2));

    let result = sub.check_constraints(&constraints, &heap_mut);
    println!("check_constraints with same symbol at different addresses: {}", result);
    println!("Expected: false (they represent the same predicate 'e')");
    println!("Actual: {} — {}", result,
        if result { "BUG: constraint bypassed!" } else { "correctly caught" }
    );

    // This is the suspected root cause of the trains infinite loop:
    // The constraint check passes because it compares heap addresses, not symbol values
    assert!(
        !result,
        "CONFIRMED BUG: Same symbol 'e' at different heap addresses bypasses constraint check"
    );
}

/// Same test but using heap.bind (the actual mechanism) instead of direct mutation
#[test]
fn same_symbol_different_address_via_heap_bind() {
    let e_sym = SymbolDB::set_const("bypass2_e".into());

    let mut heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),  // 0: 'e' — where P resolved to
        (Tag::Ref, 1),      // 1: Q ref (unbound, self-pointing)
        (Tag::Ref, 2),      // 2: R ref (unbound, self-pointing)
        (Tag::Con, e_sym),  // 3: another 'e' (e.g., from building goal Q(X))
        (Tag::Con, e_sym),  // 4: another 'e' (e.g., from building goal R(X))
    ];

    let constraints: Vec<usize> = vec![0, 1, 2];

    // Bind Q ref to the 'e' at addr 3, R ref to 'e' at addr 4
    heap.bind(&[(1, 3), (2, 4)]);

    println!("After bind: Q ref addr 1 -> {} (deref {})", heap[1].1, heap.deref_addr(1));
    println!("After bind: R ref addr 2 -> {} (deref {})", heap[2].1, heap.deref_addr(2));
    println!("P target: addr {} = {:?}", 0, heap[0]);
    println!("Q target: addr {} = {:?}", heap.deref_addr(1), heap[heap.deref_addr(1)]);
    println!("R target: addr {} = {:?}", heap.deref_addr(2), heap[heap.deref_addr(2)]);

    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    println!("check_constraints: {} (expected false)", result);
    assert!(
        !result,
        "CONFIRMED BUG: heap.bind to different addr with same Con value bypasses constraint"
    );
}

/// Verify: when bound to the SAME address, constraint correctly fails
#[test]
fn same_address_correctly_caught() {
    let e_sym = SymbolDB::set_const("same_addr_e".into());

    let mut heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),  // 0: 'e'
        (Tag::Ref, 1),      // 1: Q ref
        (Tag::Ref, 2),      // 2: R ref
    ];

    let constraints: Vec<usize> = vec![0, 1, 2];

    // Bind both Q and R to the SAME address as P (addr 0)
    heap.bind(&[(1, 0), (2, 0)]);

    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    println!("Same address binding: {} (expected false)", result);
    assert!(!result, "Binding to same address correctly fails");
}


// =============================================================================
// Group 7: Full build flow - tracing arg register population through goal building
// =============================================================================

/// Trace the exact sequence: unify → build goals → build clause → create constraints
/// for metarule P(A):-Q(A),R(A),{P,Q,R} matching goal e(X)
#[test]
fn full_build_flow_traces_arg_population() {
    use crate::heap::heap::Heap;
    use crate::resolution::build::build;
    use crate::program::clause::BitFlag64;

    let e_sym = SymbolDB::set_const("fbf_e".into());

    // Program heap: metarule P(A):-Q(A),R(A)
    let mut heap: Vec<Cell> = vec![
        // Head: P(A)
        (Tag::Func, 2), // 0
        (Tag::Arg, 0),  // 1: P
        (Tag::Arg, 1),  // 2: A
        // Body1: Q(A)
        (Tag::Func, 2), // 3
        (Tag::Arg, 2),  // 4: Q
        (Tag::Arg, 1),  // 5: A
        // Body2: R(A)
        (Tag::Func, 2), // 6
        (Tag::Arg, 3),  // 7: R
        (Tag::Arg, 1),  // 8: A
        // Goal: e(X)
        (Tag::Func, 2),    // 9
        (Tag::Con, e_sym), // 10: e
        (Tag::Ref, 11),    // 11: X (unbound)
    ];

    // Step 1: Unify head P(A) with goal e(X)
    let mut sub = unify(&heap, 0, 9).unwrap();
    println!("After unify P(A) with e(X):");
    println!("  Arg0(P) = {:?}", sub.get_arg(0));
    println!("  Arg1(A) = {:?}", sub.get_arg(1));
    println!("  Arg2(Q) = {:?}", sub.get_arg(2));
    println!("  Arg3(R) = {:?}", sub.get_arg(3));
    assert!(sub.get_arg(0).is_some(), "P should be bound after unify");
    assert!(sub.get_arg(1).is_some(), "A should be bound after unify");
    assert!(sub.get_arg(2).is_none(), "Q should be unbound after unify");
    assert!(sub.get_arg(3).is_none(), "R should be unbound after unify");

    // Step 2: Build goals (meta_vars=None, so all args get substituted)
    let goal1_addr = build(&mut heap, &mut sub, None, 3); // Q(A)
    println!("\nAfter building goal Q(A):");
    println!("  Built goal at addr {}: {}", goal1_addr, heap.term_string(goal1_addr));
    println!("  Arg2(Q) = {:?}", sub.get_arg(2));
    assert!(sub.get_arg(2).is_some(), "Q should now be set after building goal");

    let goal2_addr = build(&mut heap, &mut sub, None, 6); // R(A)
    println!("\nAfter building goal R(A):");
    println!("  Built goal at addr {}: {}", goal2_addr, heap.term_string(goal2_addr));
    println!("  Arg3(R) = {:?}", sub.get_arg(3));
    assert!(sub.get_arg(3).is_some(), "R should now be set after building goal");

    // Step 3: Examine the Ref cells created for Q and R
    let q_addr = sub.get_arg(2).unwrap();
    let r_addr = sub.get_arg(3).unwrap();
    println!("\nQ ref addr: {} -> {:?} ({})", q_addr, heap[q_addr], heap.term_string(q_addr));
    println!("R ref addr: {} -> {:?} ({})", r_addr, heap[r_addr], heap.term_string(r_addr));
    assert_ne!(q_addr, r_addr, "Q and R should be different Ref cells");

    // Step 4: Build hypothesis clause (with meta_vars)
    // meta_vars = {0(P), 2(Q), 3(R)} — these get substituted
    // A (arg 1) is NOT in meta_vars — stays as Arg
    let mut meta_vars = BitFlag64::default();
    meta_vars.set(0); // P
    meta_vars.set(2); // Q
    meta_vars.set(3); // R

    let h_head = build(&mut heap, &mut sub, Some(meta_vars), 0);
    let h_body1 = build(&mut heap, &mut sub, Some(meta_vars), 3);
    let h_body2 = build(&mut heap, &mut sub, Some(meta_vars), 6);
    println!("\nHypothesis clause:");
    println!("  Head: {}", heap.term_string(h_head));
    println!("  Body1: {}", heap.term_string(h_body1));
    println!("  Body2: {}", heap.term_string(h_body2));

    // Step 5: Create constraints (same logic as try_choices)
    let mut constraints = Vec::new();
    for i in 0..4 {
        // Check meta_vars {0, 2, 3}
        if meta_vars.get(i) {
            let addr = sub.get_arg(i);
            println!("  Constraint for arg {}: {:?}", i, addr);
            if let Some(a) = addr {
                constraints.push(a);
            }
        }
    }
    println!("\nConstraints: {:?}", constraints);
    println!("  Constraint[0] (P) addr {} -> {}", constraints[0], heap.term_string(constraints[0]));
    println!("  Constraint[1] (Q) addr {} -> {}", constraints[1], heap.term_string(constraints[1]));
    println!("  Constraint[2] (R) addr {} -> {}", constraints[2], heap.term_string(constraints[2]));

    // Step 6: Check — all three constraint addresses should be different at this point
    let result = sub.check_constraints(&constraints, &heap);
    println!("\ncheck_constraints on self (all unbound): {}", result);
    println!("  P resolves to: {}", heap.term_string(heap.deref_addr(constraints[0])));
    println!("  Q resolves to: {}", heap.term_string(heap.deref_addr(constraints[1])));
    println!("  R resolves to: {}", heap.term_string(heap.deref_addr(constraints[2])));

    // Step 7: Simulate what happens when body goals are proved
    // Q(east1) matches short(east1) — the Ref for Q gets bound to 'short'
    // R(east1) matches closed(east1) — the Ref for R gets bound to 'closed'
    // In the actual system this happens via heap.bind() from subsequent proof steps
    // But the constraint check should work when these refs are later bound

    let short_sym = SymbolDB::set_const("fbf_short".into());
    let closed_sym = SymbolDB::set_const("fbf_closed".into());
    let short_addr = heap.heap_push((Tag::Con, short_sym));
    let closed_addr = heap.heap_push((Tag::Con, closed_sym));

    // Bind Q ref -> short, R ref -> closed
    heap.bind(&[(q_addr, short_addr), (r_addr, closed_addr)]);
    println!("\nAfter binding Q=short, R=closed:");
    println!("  Q ref addr {} -> {}", q_addr, heap.term_string(q_addr));
    println!("  R ref addr {} -> {}", r_addr, heap.term_string(r_addr));
    println!("  Constraint[1] (Q) -> {}", heap.term_string(constraints[1]));
    println!("  Constraint[2] (R) -> {}", heap.term_string(constraints[2]));

    // Now check constraints — P=e, Q=short, R=closed — all different, should pass
    let default_sub = Substitution::default();
    let result_good = default_sub.check_constraints(&constraints, &heap);
    println!("  check_constraints (P=e, Q=short, R=closed): {}", result_good);
    assert!(result_good, "Different bindings should pass");

    // Now simulate the BAD case: Q=e, R=e (both bound to same as P)
    heap.unbind(&[(q_addr, short_addr), (r_addr, closed_addr)]);
    let e_addr = sub.get_arg(0).unwrap(); // P's target = 'e'
    heap.bind(&[(q_addr, e_addr), (r_addr, e_addr)]);
    println!("\nAfter binding Q=e, R=e (same as P):");
    println!("  P constraint {} -> {}", constraints[0], heap.term_string(constraints[0]));
    println!("  Q constraint {} -> {}", constraints[1], heap.term_string(constraints[1]));
    println!("  R constraint {} -> {}", constraints[2], heap.term_string(constraints[2]));

    let result_bad = default_sub.check_constraints(&constraints, &heap);
    println!("  check_constraints (P=Q=R=e): {}", result_bad);
    // This SHOULD fail — all three resolve to 'e'
    assert!(
        !result_bad,
        "P=Q=R=e should fail constraint check, but got: {}",
        result_bad
    );
}

/// Test the critical timing: constraints are checked against EXISTING hypothesis
/// constraints. When proving body goals, subsequent metarule matches check against
/// constraints from the parent clause. But the parent clause's Q/R refs are unbound
/// at that point — they only get bound when the child goals succeed.
#[test]
fn constraint_timing_during_proof() {
    use crate::heap::heap::Heap;

    let e_sym = SymbolDB::set_const("ctp_e".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),  // 0: e
        (Tag::Ref, 1),      // 1: unbound (Q's ref from goal build)
        (Tag::Ref, 2),      // 2: unbound (R's ref from goal build)
    ];

    // Constraints from the first hypothesis clause: [P_addr=0, Q_addr=1, R_addr=2]
    let constraints: Vec<usize> = vec![0, 1, 2];

    // At the time the child goals are being proved, Q and R refs are still unbound
    // A new metarule match creates a substitution. Does check_constraints on the
    // parent's constraints correctly handle unbound refs?
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    println!("Constraints with unbound Q, R refs: {}", result);
    println!("  P (addr 0) deref -> addr {}", heap.deref_addr(0));
    println!("  Q (addr 1) deref -> addr {}", heap.deref_addr(1));
    println!("  R (addr 2) deref -> addr {}", heap.deref_addr(2));
    // P deref -> 0 (Con e), Q deref -> 1 (self-ref), R deref -> 2 (self-ref)
    // All different addresses → passes. This is correct at this stage.
    assert!(result, "With unbound Q, R, all constraint targets differ");
}

/// What happens in the actual scenario where Q's body goal matches e
/// (the same predicate as P)?
/// When goal Q(east1) is tried and matches metarule again with Q=e,
/// does the constraint from the parent clause catch P=Q=e?
#[test]
fn constraint_detects_q_binding_to_e() {
    use crate::heap::heap::Heap;

    let e_sym = SymbolDB::set_const("cdq_e".into());

    let mut heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),  // 0: e
        (Tag::Ref, 1),      // 1: Q's ref (from goal build, currently unbound)
        (Tag::Ref, 2),      // 2: R's ref (from goal build, currently unbound)
    ];

    // Parent clause constraints: [P=addr0, Q=addr1, R=addr2]
    let constraints: Vec<usize> = vec![0, 1, 2];

    // Now, during proof of goal Q(east1), the system matches against a clause.
    // If Q's ref (addr 1) gets bound to 'e' (addr 0) via heap.bind:
    heap.bind(&[(1, 0)]);
    println!("After binding Q ref (addr 1) -> e (addr 0):");
    println!("  addr 0 deref = {}", heap.deref_addr(0));
    println!("  addr 1 deref = {}", heap.deref_addr(1));
    println!("  addr 2 deref = {}", heap.deref_addr(2));

    // Now constraint addrs 0 and 1 should both resolve to addr 0
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    println!("check_constraints after Q bound to e: {}", result);
    assert!(
        !result,
        "After Q is bound to same as P, constraint should FAIL, got: {}",
        result
    );
}

/// But wait — binding Q's ref happens via heap.bind during proof,
/// NOT via the substitution. The constraint check uses full_deref
/// which follows heap refs. So if Q's ref cell points to e on the heap,
/// check_constraints should see it through heap deref alone.
#[test]
fn constraint_check_follows_heap_bindings() {
    use crate::heap::heap::Heap;

    let e_sym = SymbolDB::set_const("ccfh_e".into());
    let short_sym = SymbolDB::set_const("ccfh_short".into());

    let mut heap: Vec<Cell> = vec![
        (Tag::Con, e_sym),    // 0: e
        (Tag::Ref, 1),        // 1: Q ref (unbound)
        (Tag::Ref, 2),        // 2: R ref (unbound)
        (Tag::Con, short_sym),// 3: short
    ];

    let constraints: Vec<usize> = vec![0, 1, 2];

    // Before any binding — all different
    let sub = Substitution::default();
    assert!(sub.check_constraints(&constraints, &heap), "All unbound = all different");

    // Bind Q -> short (different from P=e)
    heap.bind(&[(1, 3)]);
    assert!(sub.check_constraints(&constraints, &heap), "P=e, Q=short, R=unbound = ok");

    // Unbind Q, then bind Q -> e (same as P)
    heap.unbind(&[(1, 3)]);
    heap.bind(&[(1, 0)]);
    let result = sub.check_constraints(&constraints, &heap);
    println!("P=e, Q=e (via heap bind), R=unbound: {}", result);
    assert!(!result, "P=Q=e should fail even with empty substitution");
}


// =============================================================================
// Group 8: Child goal matching - does constraint check catch Q binding to e
// via a DIFFERENT heap address for the same symbol?
// =============================================================================

/// Simulate the full scenario:
/// 1. Metarule P(A):-Q(A),R(A) matches e(east1), creating hypothesis clause
/// 2. Constraints stored: [P_con_addr, Q_ref_addr, R_ref_addr]
/// 3. Child goal Q(east1) tries to match hypothesis clause e(A):-e(A),e(A)
/// 4. Unification binds Q_ref → hypothesis clause's Con(e) (a DIFFERENT address)
/// 5. Does check_constraints detect that Q now points to 'e' like P?
#[test]
fn child_goal_q_matches_hypothesis_e_different_addr() {
    use crate::heap::heap::Heap;
    use crate::program::clause::BitFlag64;

    let e_sym = SymbolDB::set_const("cgm_e".into());
    let east1_sym = SymbolDB::set_const("cgm_east1".into());

    // === Phase 1: Set up the program heap with metarule and goal ===

    let mut heap: Vec<Cell> = vec![
        // Metarule head: P(A) — addr 0
        (Tag::Func, 2), // 0
        (Tag::Arg, 0),  // 1: P
        (Tag::Arg, 1),  // 2: A
        // Metarule body1: Q(A) — addr 3
        (Tag::Func, 2), // 3
        (Tag::Arg, 2),  // 4: Q
        (Tag::Arg, 1),  // 5: A
        // Metarule body2: R(A) — addr 6
        (Tag::Func, 2), // 6
        (Tag::Arg, 3),  // 7: R
        (Tag::Arg, 1),  // 8: A
        // Goal: e(east1) — addr 9
        (Tag::Func, 2),       // 9
        (Tag::Con, e_sym),    // 10: e  <-- P will point here
        (Tag::Con, east1_sym),// 11: east1
    ];

    // === Phase 2: Unify metarule head with goal ===
    let mut sub = unify(&heap, 0, 9).unwrap();
    println!("Phase 2 - After unify P(A) with e(east1):");
    println!("  Arg0(P) = {:?}", sub.get_arg(0));  // Some(10) = Con e
    println!("  Arg1(A) = {:?}", sub.get_arg(1));  // Some(11) = Con east1
    println!("  Arg2(Q) = {:?}", sub.get_arg(2));  // None
    println!("  Arg3(R) = {:?}", sub.get_arg(3));  // None

    // === Phase 3: Build goals (meta_vars=None) ===
    let goal_q = build(&mut heap, &mut sub, None, 3);
    let goal_r = build(&mut heap, &mut sub, None, 6);
    println!("\nPhase 3 - Built goals:");
    println!("  Goal Q(east1) at addr {}: {}", goal_q, heap.term_string(goal_q));
    println!("  Goal R(east1) at addr {}: {}", goal_r, heap.term_string(goal_r));
    let q_ref_addr = sub.get_arg(2).unwrap();
    let r_ref_addr = sub.get_arg(3).unwrap();
    println!("  Q predicate Ref at addr {}: {:?}", q_ref_addr, heap[q_ref_addr]);
    println!("  R predicate Ref at addr {}: {:?}", r_ref_addr, heap[r_ref_addr]);

    // === Phase 4: Build hypothesis clause and constraints ===
    let mut meta_vars = BitFlag64::default();
    meta_vars.set(0); // P
    meta_vars.set(2); // Q
    meta_vars.set(3); // R

    let _h_head = build(&mut heap, &mut sub, Some(meta_vars), 0);
    let _h_body1 = build(&mut heap, &mut sub, Some(meta_vars), 3);
    let _h_body2 = build(&mut heap, &mut sub, Some(meta_vars), 6);

    let mut constraints = Vec::new();
    for i in [0usize, 2, 3] {
        constraints.push(sub.get_arg(i).unwrap());
    }
    println!("\nPhase 4 - Constraints: {:?}", constraints);
    println!("  P constraint addr {} -> {} ({:?})", constraints[0], heap.term_string(constraints[0]), heap[constraints[0]]);
    println!("  Q constraint addr {} -> {} ({:?})", constraints[1], heap.term_string(constraints[1]), heap[constraints[1]]);
    println!("  R constraint addr {} -> {} ({:?})", constraints[2], heap.term_string(constraints[2]), heap[constraints[2]]);

    // Apply parent bindings to heap (as prove() does after try_choices succeeds)
    let parent_bindings = sub.get_bindings();
    heap.bind(&parent_bindings);
    println!("\nPhase 4b - After applying parent bindings to heap:");
    println!("  Q ref {} now -> {} ({:?})", q_ref_addr, heap.term_string(q_ref_addr), heap[q_ref_addr]);
    println!("  R ref {} now -> {} ({:?})", r_ref_addr, heap.term_string(r_ref_addr), heap[r_ref_addr]);

    // === Phase 5: Child goal Q(east1) tries to match ===
    // The hypothesis clause e(A):-e(A),e(A) has its 'e' at BUILT addresses
    // Let's simulate: the hypothesis clause head is e(A) built at some addr
    // It has a Con(e_sym) at a DIFFERENT address than addr 10
    
    // Find the hypothesis head we just built - it has e(A) with e at a new addr
    println!("\nPhase 5 - Hypothesis clause head: {}", heap.term_string(_h_head));
    // The Con(e) in the hypothesis head is at _h_head + 1
    let hyp_e_addr = _h_head + 1;
    println!("  Hypothesis 'e' at addr {}: {:?}", hyp_e_addr, heap[hyp_e_addr]);
    // This should be a Ref pointing to the original e (addr 10), not a new Con
    // because build with meta_vars set for P creates: set_ref(Some(addr_10))
    println!("  Deref of hyp_e_addr: {} ({:?})", heap.deref_addr(hyp_e_addr), heap[heap.deref_addr(hyp_e_addr)]);

    // Now simulate unifying child goal Q(east1) with hypothesis head e(A)
    // Child goal Q(east1) is at addr goal_q
    // The Q predicate is a Ref at q_ref_addr
    // Hypothesis head e(A) is at _h_head
    // The e predicate is at hyp_e_addr (which is a Ref -> 10, the Con(e))
    
    println!("\n  Child goal addr {}: {}", goal_q, heap.term_string(goal_q));
    println!("  Hypothesis head addr {}: {}", _h_head, heap.term_string(_h_head));
    
    let child_sub = unify(&heap, _h_head, goal_q);
    match &child_sub {
        Some(s) => {
            println!("  Unification succeeded!");
            println!("  Child sub bindings: {:?}", s.get_bindings());
            
            // Now check the parent's constraints with the child's substitution
            let result = s.check_constraints(&constraints, &heap);
            println!("\n  check_constraints (parent constraints, child sub): {}", result);
            
            // Trace through full_deref for each constraint
            for (label, &c_addr) in ["P", "Q", "R"].iter().zip(constraints.iter()) {
                let heap_deref = heap.deref_addr(c_addr);
                let full_deref_target = s.full_deref(c_addr, &heap);
                println!("  {} constraint addr {} -> heap_deref {} -> full_deref {}", 
                    label, c_addr, heap_deref, full_deref_target);
                println!("    heap_deref cell: {:?} = {}", heap[heap_deref], heap.term_string(heap_deref));
                println!("    full_deref cell: {:?} = {}", heap[full_deref_target], heap.term_string(full_deref_target));
            }
            
            // The key question: does P's full_deref == Q's full_deref?
            let p_target = s.full_deref(constraints[0], &heap);
            let q_target = s.full_deref(constraints[1], &heap);
            let r_target = s.full_deref(constraints[2], &heap);
            println!("\n  P target addr: {}", p_target);
            println!("  Q target addr: {}", q_target);
            println!("  R target addr: {}", r_target);
            println!("  P == Q? {} (SHOULD be true if both resolve to 'e')", p_target == q_target);
            
            if p_target == q_target {
                println!("  ✓ Constraint correctly detects P=Q");
                assert!(!result, "Constraint should FAIL when Q resolves to same as P");
            } else {
                println!("  ✗ Constraint FAILS to detect P=Q!");
                println!("    P resolves to addr {} ({:?})", p_target, heap[p_target]);
                println!("    Q resolves to addr {} ({:?})", q_target, heap[q_target]);
                println!("    These are DIFFERENT addresses but same symbol!");
                
                // Check if it's the same symbol even at different addresses
                let p_cell = heap[p_target];
                let q_cell = heap[q_target];
                if p_cell == q_cell {
                    println!("    BUG CONFIRMED: Same cell value {:?} at different addresses", p_cell);
                    println!("    check_constraints compares ADDRESSES not VALUES");
                    // This assertion documents the bug
                    assert!(result, "Bug: constraint passes despite P and Q having same symbol");
                }
            }
        }
        None => {
            println!("  Unification failed (unexpected)");
        }
    }
}

/// Simpler version: directly test whether check_constraints catches
/// two Con cells with the same symbol ID at different addresses
#[test]
fn constraints_same_symbol_different_addresses() {
    let sym = SymbolDB::set_const("csda_test".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, sym),  // addr 0: Con(test)
        (Tag::Con, sym),  // addr 1: Con(test) - same symbol, different address
        (Tag::Con, sym),  // addr 2: Con(test) - same symbol, different address
    ];

    let constraints: Vec<usize> = vec![0, 1, 2];
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);
    
    println!("Three Con cells with same symbol at different addresses:");
    println!("  addr 0: {:?}", heap[0]);
    println!("  addr 1: {:?}", heap[1]);
    println!("  addr 2: {:?}", heap[2]);
    println!("  check_constraints result: {}", result);
    
    // full_deref on a Con cell returns the cell's own address (no ref chain)
    // So targets are [0, 1, 2] - all different addresses
    // Even though they represent the same symbol!
    if result {
        println!("  BUG: Constraint PASSES despite all being same symbol");
        println!("  check_constraints compares final ADDRESSES, not cell VALUES");
    } else {
        println!("  Constraint correctly rejects same symbols");
    }
}

/// Test with Ref chains: refs to different Con cells with same symbol
#[test]
fn constraints_refs_to_same_symbol_different_con_addrs() {
    let sym = SymbolDB::set_const("crsd_test".into());

    let heap: Vec<Cell> = vec![
        (Tag::Con, sym),  // addr 0: Con(test)
        (Tag::Con, sym),  // addr 1: Con(test) - duplicate
        (Tag::Ref, 0),    // addr 2: Ref -> 0
        (Tag::Ref, 1),    // addr 3: Ref -> 1
    ];

    // Constraints point to the refs
    let constraints: Vec<usize> = vec![2, 3];
    let sub = Substitution::default();
    let result = sub.check_constraints(&constraints, &heap);

    println!("Two refs pointing to different Con cells with same symbol:");
    println!("  Ref at 2 -> deref to addr 0: {:?}", heap[0]);
    println!("  Ref at 3 -> deref to addr 1: {:?}", heap[1]);
    println!("  check_constraints: {}", result);
    
    // full_deref(2) → heap deref → 0 (Con), full_deref(3) → heap deref → 1 (Con)
    // Targets are addr 0 and addr 1 - different addresses!
    if result {
        println!("  BUG: Passes because addrs 0 != 1, even though both are Con(same_sym)");
    }
}
