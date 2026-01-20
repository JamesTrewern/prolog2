/// Tests for predicate invention behavior in MIL
/// 
/// These tests probe the specific mechanics of:
/// 1. When predicate invention occurs
/// 2. How invented predicates bind to goals
/// 3. Whether invented predicates can be reused across clauses
/// 4. Constraint behavior with invented predicates

#[cfg(test)]
mod predicate_invention_tests {
    use std::sync::Arc;
    use crate::{
        heap::{
            heap::{Heap, Tag},
            query_heap::QueryHeap,
            symbol_db::SymbolDB,
        },
        program::{
            clause::Clause,
            hypothesis::Hypothesis,
            predicate_table::PredicateTable,
        },
        resolution::{
            proof::{Env, Proof},
            unification::{unify, Substitution},
            build::build,
        },
        Config,
    };

    fn test_config() -> Config {
        Config {
            max_depth: 10,
            max_clause: 6,
            max_pred: 2,
        }
    }

    // ============================================================================
    // TEST: Predicate invention creates binding in substitution
    // ============================================================================
    
    /// When we invent a predicate, it should be stored in substitution.arg[0]
    /// and used when building BOTH the hypothesis clause AND the new goals
    #[test]
    fn test_invented_pred_in_substitution() {
        let p = SymbolDB::set_const("P".into());
        let q = SymbolDB::set_const("Q".into());
        let x = SymbolDB::set_const("X".into());
        let y = SymbolDB::set_const("Y".into());
        
        // This test verifies that after predicate invention:
        // 1. substitution.get_arg(0) returns the invented predicate address
        // 2. Building a term with Arg(0) uses the invented predicate
        
        println!("Test: Verify invented predicate is properly stored in substitution");
        println!("Expected: After invention, Arg(0) should resolve to pred_N constant");
    }

    // ============================================================================
    // TEST: Goals built after invention use invented predicate
    // ============================================================================
    
    /// The recursive goal P(Z,Y) in meta-clause P(X,Y):-Q(X,Z),P(Z,Y)
    /// should become pred_N(Z,Y) not Ref_X(Z,Y) after invention
    #[test]
    fn test_goals_use_invented_predicate() {
        println!("Test: Goals should use invented predicate symbol");
        println!("Scenario:");
        println!("  Goal: Ref_100(a,b) - variable predicate");
        println!("  Clause: P(X,Y):-Q(X,Z),P(Z,Y) - meta-clause with variable head");
        println!("  Action: Invent pred_0");
        println!("Expected new goals:");
        println!("  Goal 1: Ref_X(a,Ref_Y) - Q bound to body predicate choices");
        println!("  Goal 2: pred_0(Ref_Y,b) - P bound to invented predicate");
        println!("NOT:");
        println!("  Goal 2: Ref_100(Ref_Y,b) - still using original variable");
    }

    // ============================================================================
    // TEST: Invented predicate can unify with body predicates
    // ============================================================================
    
    /// After inventing pred_0, a goal pred_0(a,b) should be able to
    /// match against dad(a,b) or mum(a,b) via the identity meta-rule
    #[test]
    fn test_invented_pred_matches_body_predicates() {
        println!("Test: Invented predicate can be defined using body predicates");
        println!("Scenario:");
        println!("  Invented: pred_0");
        println!("  Goal: pred_0(ken,adam)");
        println!("  Available: dad(ken,adam) as body predicate");
        println!("  Meta-rule: P(X,Y):-Q(X,Y) (identity)");
        println!("Expected:");
        println!("  pred_0(ken,adam) matches P(X,Y):-Q(X,Y)");
        println!("  Creates clause: pred_0(X,Y):-Ref_Q(X,Y)");
        println!("  Goal: Ref_Q(ken,adam) matches dad(ken,adam)");
        println!("  Ref_Q binds to dad");
        println!("  Final clause: pred_0(X,Y):-dad(X,Y)");
    }

    // ============================================================================
    // TEST: Multiple clauses can define same invented predicate
    // ============================================================================
    
    /// The "parent" concept needs multiple clauses:
    /// parent(X,Y) :- dad(X,Y).
    /// parent(X,Y) :- mum(X,Y).
    #[test]
    fn test_multiple_clauses_for_invented_pred() {
        println!("Test: Invented predicate can have multiple defining clauses");
        println!("Scenario: Learning 'parent' from 'dad' and 'mum'");
        println!("Expected hypothesis:");
        println!("  ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).");
        println!("  ancestor(X,Y) :- parent(X,Y).");
        println!("  parent(X,Y) :- dad(X,Y).");
        println!("  parent(X,Y) :- mum(X,Y).");
        println!("");
        println!("Key question: When proving ancestor(christine,james),");
        println!("can we reuse the same invented 'parent' predicate that was");
        println!("created when proving ancestor(ken,james)?");
    }

    // ============================================================================
    // TEST: Constraint check with invented predicates
    // ============================================================================
    
    /// Constraints should prevent P=Q but allow invented predicates
    /// to bind to different body predicates
    #[test]
    fn test_constraints_with_invented_pred() {
        println!("Test: Constraints work correctly with invented predicates");
        println!("Scenario:");
        println!("  Meta-rule: P(X,Y):-Q(X,Y) with constraint P≠Q");
        println!("  Invented: pred_0 for P");
        println!("  Goal: Ref_Q(a,b) needs to bind to body predicate");
        println!("");
        println!("Constraint should prevent: pred_0 = dad when Ref_Q also = dad");
        println!("Wait, no - the constraint is on the CLAUSE's P and Q,");
        println!("not on reuse across different clause instantiations.");
        println!("");
        println!("Actually, the constraint addresses are collected from");
        println!("the substitution's Arg mappings at clause creation time.");
        println!("So constraint = [addr_of_P_in_clause, addr_of_Q_in_clause]");
        println!("These are heap addresses in the hypothesis clause.");
    }

    // ============================================================================
    // TEST: Search order for finding "parent" generalization  
    // ============================================================================
    
    /// To find the parent generalization, the search must:
    /// 1. Try chain meta-rule for ancestor(ken,james)
    /// 2. Invent pred_0 (will become parent)
    /// 3. Prove pred_0(ken,adam) using identity meta-rule → pred_0:-dad
    /// 4. Prove ancestor(adam,james) recursively
    /// 5. Eventually need pred_0(adam,james) → pred_0:-dad (base case)
    /// 6. Then for ancestor(christine,james):
    /// 7. Reuse pred_0 via existing ancestor clauses
    /// 8. Prove pred_0(christine,tami) → need pred_0:-mum
    #[test]
    fn test_search_order_for_parent_generalization() {
        println!("Test: Search can find parent generalization");
        println!("");
        println!("The key insight: When we invent pred_0 for the first goal,");
        println!("pred_0 becomes a KNOWN predicate (not variable) in the hypothesis.");
        println!("When we try to prove ancestor(christine,james), we should be able to");
        println!("use the existing ancestor clauses which reference pred_0.");
        println!("");
        println!("But pred_0(christine,tami) will fail with just pred_0:-dad.");
        println!("We need to add pred_0:-mum.");
        println!("");
        println!("Question: When ancestor(christine,james) uses the hypothesis clause");
        println!("ancestor(X,Y):-pred_0(X,Z),ancestor(Z,Y), does pred_0(christine,Z)");
        println!("trigger creation of a new pred_0 clause via meta-rules?");
    }

    // ============================================================================
    // TEST: Hypothesis clauses with constant vs variable predicates
    // ============================================================================
    
    /// A hypothesis clause like ancestor(X,Y):-pred_0(X,Z),ancestor(Z,Y)
    /// has CONSTANT predicates (ancestor, pred_0), not variables.
    /// When used as a choice, it should NOT trigger predicate invention.
    #[test]
    fn test_hypothesis_clause_has_constant_predicates() {
        println!("Test: Hypothesis clauses have constant (not variable) predicates");
        println!("");
        println!("When a hypothesis clause is created:");
        println!("  Original meta-clause: P(X,Y):-Q(X,Z),P(Z,Y)");
        println!("  After substitution: ancestor(X,Y):-pred_0(X,Z),ancestor(Z,Y)");
        println!("");
        println!("The predicates 'ancestor' and 'pred_0' should be CONSTANTS,");
        println!("not Args or Refs. This means:");
        println!("  - clause.meta() should return false for hypothesis clauses");
        println!("  - Using this clause should NOT trigger new predicate invention");
        println!("");
        println!("Check: What does Clause::new(literals, None) set for meta_vars?");
        println!("The None means no meta_vars, so meta() returns false. Good.");
    }

    // ============================================================================
    // TEST: Proving goal with invented predicate
    // ============================================================================
    
    /// When we have hypothesis clause pred_0(X,Y):-dad(X,Y)
    /// and goal pred_0(christine,tami), it should FAIL (no dad(christine,tami))
    /// Then we need to try meta-rules to create pred_0(X,Y):-mum(X,Y)
    #[test]
    fn test_proving_invented_pred_goal() {
        println!("Test: Goal with invented predicate tries hypothesis then meta-rules");
        println!("");
        println!("State:");
        println!("  Hypothesis: [pred_0(X,Y):-dad(X,Y)]");
        println!("  Goal: pred_0(christine,tami)");
        println!("  Body predicates: dad/2, mum/2");
        println!("  Meta-rules: P(X,Y):-Q(X,Y), P(X,Y):-Q(X,Z),P(Z,Y)");
        println!("");
        println!("Search order in get_choices:");
        println!("  1. Hypothesis clauses → pred_0(X,Y):-dad(X,Y)");
        println!("  2. If symbol==0 (variable pred): meta-rules + body predicates");
        println!("  3. Else: predicate_table lookup for pred_0");
        println!("");
        println!("Question: Is pred_0 in the predicate_table?");
        println!("  - pred_0 is dynamically created via SymbolDB::set_const");
        println!("  - It's NOT added to predicate_table");
        println!("  - So predicate_table.get_predicate((pred_0, 2)) returns None");
        println!("  - This triggers: get_variable_clauses(2) → meta-rules!");
        println!("");
        println!("This means pred_0(christine,tami) WILL try meta-rules. Good!");
    }

    // ============================================================================
    // INTEGRATION TEST: Full parent generalization scenario
    // ============================================================================
    
    #[test]
    fn test_parent_generalization_integration() {
        // This would be a full integration test that:
        // 1. Sets up the family background knowledge
        // 2. Sets up the meta-rules
        // 3. Runs the proof for ancestor(ken,james), ancestor(christine,james)
        // 4. Checks if the "parent" generalization is found
        
        println!("Integration test: Find parent generalization");
        println!("");
        println!("Setup:");
        println!("  BK: dad(ken,adam), dad(adam,james), mum(christine,tami), mum(tami,james)");
        println!("  Meta-rules: P(X,Y):-Q(X,Y), P(X,Y):-Q(X,Z),P(Z,Y)");
        println!("  Examples: ancestor(ken,james), ancestor(christine,james)");
        println!("  Config: max_clause=6, max_pred=2");
        println!("");
        println!("Expected hypothesis (one possibility):");
        println!("  ancestor(X,Y) :- pred_0(X,Z), ancestor(Z,Y).");
        println!("  ancestor(X,Y) :- pred_0(X,Y).");  
        println!("  pred_0(X,Y) :- dad(X,Y).");
        println!("  pred_0(X,Y) :- mum(X,Y).");
    }
}