use std::collections::HashMap;

use super::{
    build_tree::TreeClause,
    term::{Term, Unit},
};
use crate::{
    heap::heap::Heap,
    program::{clause::Clause, predicate_table::PredicateTable},
};

pub fn build_clause(
    literals: Vec<Term>,
    meta_vars: Option<Vec<String>>,
    constrained_vars: Option<Vec<String>>,
    heap: &mut impl Heap,
    query: bool,
) -> Clause {
    let mut var_values = HashMap::new();

    let literals: Vec<usize> = literals
        .into_iter()
        .map(|term| term.encode(heap, &mut var_values, query))
        .collect();

    let meta_vars = meta_vars.map(|vars| {
        vars.into_iter()
            .map(|var| *var_values.get(&var).unwrap())
            .collect::<Vec<usize>>()
    });

    let constrained_vars = constrained_vars.map(|vars| {
        vars.into_iter()
            .map(|var| *var_values.get(&var).unwrap())
            .collect::<Vec<usize>>()
    });

    Clause::new(literals, meta_vars, constrained_vars)
}

/// Extract variable names from a Term::Set
fn extract_var_names_from_set(term: Term) -> Vec<String> {
    if let Term::Set(set_terms) = term {
        set_terms
            .into_iter()
            .map(|t| {
                if let Term::Unit(Unit::Variable(symbol)) = t {
                    symbol
                } else {
                    panic!("meta variable set should only contain variables")
                }
            })
            .collect()
    } else {
        panic!("Expected a Set term")
    }
}

/// Extract variable names from a Term::List (must be a flat list with EmptyList tail)
fn extract_var_names_from_list(term: Term) -> Vec<String> {
    if let Term::List(list_terms, tail) = term {
        assert!(
            matches!(*tail, Term::EmptyList),
            "Unconstrained variable list must not have a tail"
        );
        list_terms
            .into_iter()
            .map(|t| {
                if let Term::Unit(Unit::Variable(symbol)) = t {
                    symbol
                } else {
                    panic!("unconstrained variable list should only contain variables")
                }
            })
            .collect()
    } else {
        panic!("Expected a List term")
    }
}

/// Extract meta_vars and constrained_vars from a MetaRule's trailing terms.
///
/// Handles three cases:
/// - `...{P,Q,R}.` → meta_vars = {P,Q,R}, constrained_vars = None (defaults to all)
/// - `...{P},[Q1,Q2].` → meta_vars = {P,Q1,Q2}, constrained_vars = Some({P})
/// - `...[Q1,Q2].` → meta_vars = {Q1,Q2}, constrained_vars = Some({}) (empty)
fn extract_meta_rule_vars(terms: &mut Vec<Term>) -> (Vec<String>, Option<Vec<String>>) {
    let last = terms.pop().unwrap();
    match last {
        // Case 1: last is {P,Q,R} — all constrained (original behaviour)
        Term::Set(_) => {
            let meta_vars = extract_var_names_from_set(last);
            (meta_vars, None)
        }
        // Case 2 or 3: last is [Q1,Q2]
        Term::List(_, _) => {
            let unconstrained = extract_var_names_from_list(last);
            // Check if the new last element is a Set (Case 2: {P},[Q1,Q2])
            let constrained = if matches!(terms.last(), Some(Term::Set(_))) {
                extract_var_names_from_set(terms.pop().unwrap())
            } else {
                // Case 3: [Q1,Q2] only — no constrained vars
                Vec::new()
            };
            let mut meta_vars = constrained.clone();
            meta_vars.extend(unconstrained);
            (meta_vars, Some(constrained))
        }
        _ => panic!("Last literal in meta_rule wasn't a set or list"),
    }
}

// pub fn execute_directive(directive: Vec<Term>, predicate_table: &mut PredicateTable) -> Result<(),String>{
//     let mut heap = QueryHeap::new(None)?;
//     let goals = build_clause(directive, None, &mut heap, true);
//     //TODO Find Variables in goals to report bindings once solved
//     let proof = Proof::new(heap, &goals, predicate_table);

//     Ok(())
// }

pub(crate) fn execute_tree(
    syntax_tree: Vec<TreeClause>,
    heap: &mut impl Heap,
    pred_table: &mut PredicateTable,
) {
    for clause in syntax_tree {
        match clause {
            TreeClause::Fact(term) => {
                let clause = build_clause(vec![term], None, None, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table
                    .add_clause_to_predicate(clause, symbol_arity)
                    .unwrap();
            }
            TreeClause::Rule(terms) => {
                let clause = build_clause(terms, None, None, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table
                    .add_clause_to_predicate(clause, symbol_arity)
                    .unwrap();
            }
            TreeClause::MetaRule(mut terms) => {
                let (meta_vars, constrained_vars) = extract_meta_rule_vars(&mut terms);
                let clause = build_clause(terms, Some(meta_vars), constrained_vars, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table
                    .add_clause_to_predicate(clause, symbol_arity)
                    .unwrap();
            }
            TreeClause::MetaFact(head, meta_data) => {
                let meta_vars = extract_var_names_from_set(meta_data);
                let clause = build_clause(vec![head], Some(meta_vars), None, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table
                    .add_clause_to_predicate(clause, symbol_arity)
                    .unwrap();
            }
            TreeClause::Directive(_terms) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        heap::{
            heap::{Cell, Tag},
            symbol_db::SymbolDB,
        },
        parser::execute_tree::execute_tree,
        program::predicate_table::{Predicate, PredicateTable},
    };

    use super::super::{
        build_tree::{TokenStream},
        tokeniser::tokenise,
    };

    #[test]
    fn facts() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(a,b).q(c).".into()).unwrap())
            .parse_all()
            .unwrap();

        let [p, q, a, b, c] = ["p", "q", "a", "b", "c"].map(|s| SymbolDB::set_const(s.into()));

        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let fact = &clauses[0];
            assert_eq!(
                &heap[fact[0]..fact[0] + 4],
                &[(Tag::Func, 3), (Tag::Con, p), (Tag::Con, a), (Tag::Con, b),]
            );
        } else {
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
            let fact = &clauses[0];
            assert_eq!(
                &heap[fact[0]..fact[0] + 3],
                &[(Tag::Func, 2), (Tag::Con, q), (Tag::Con, c),]
            );
        } else {
            panic!()
        }
    }

    #[test]
    fn rules() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(
            tokenise("p(X,Y):-q(X,a),q(Y,b). q(X):-r(X). q(X):-p(X).".into()).unwrap(),
        )
        .parse_all()
        .unwrap();

        let [p, q, r, a, b] = ["p", "q", "r", "a", "b"].map(|s| SymbolDB::set_const(s.into()));

        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let rule = &clauses[0];
            assert_eq!(
                &heap[rule[0]..rule[0] + 4],
                &[(Tag::Func, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 1),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 4],
                &[(Tag::Func, 3), (Tag::Con, q), (Tag::Arg, 0), (Tag::Con, a),]
            );
            assert_eq!(
                &heap[rule[2]..rule[2] + 4],
                &[(Tag::Func, 3), (Tag::Con, q), (Tag::Arg, 1), (Tag::Con, b),]
            );
        } else {
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
            let rule = &clauses[0];
            assert_eq!(
                &heap[rule[0]..rule[0] + 3],
                &[(Tag::Func, 2), (Tag::Con, q), (Tag::Arg, 0),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 3],
                &[(Tag::Func, 2), (Tag::Con, r), (Tag::Arg, 0),]
            );

            let rule = &clauses[1];
            assert_eq!(
                &heap[rule[0]..rule[0] + 3],
                &[(Tag::Func, 2), (Tag::Con, q), (Tag::Arg, 0),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 3],
                &[(Tag::Func, 2), (Tag::Con, p), (Tag::Arg, 0),]
            );
        } else {
            panic!()
        }
    }

    #[test]
    fn meta_rules() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(X,Y):-Q(X,a),R(Y,b),{Q,R}.".into()).unwrap())
            .parse_all()
            .unwrap();

        let [p, _q, _r, a, b] = ["p", "q", "r", "a", "b"].map(|s| SymbolDB::set_const(s.into()));

        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let meta_rule = &clauses[0];
            assert_eq!(
                &heap[meta_rule[0]..meta_rule[0] + 4],
                &[(Tag::Func, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 1),]
            );
            assert_eq!(
                &heap[meta_rule[1]..meta_rule[1] + 4],
                &[(Tag::Func, 3), (Tag::Arg, 2), (Tag::Arg, 0), (Tag::Con, a),]
            );
            assert_eq!(
                &heap[meta_rule[2]..meta_rule[2] + 4],
                &[(Tag::Func, 3), (Tag::Arg, 3), (Tag::Arg, 1), (Tag::Con, b),]
            );
            assert!(meta_rule.meta_var(2).unwrap());
            assert!(meta_rule.meta_var(3).unwrap());
            // With {Q,R} only, constrained_vars defaults to same as meta_vars
            assert!(meta_rule.constrained_var(2));
            assert!(meta_rule.constrained_var(3));
            assert!(!meta_rule.constrained_var(0));
            assert!(!meta_rule.constrained_var(1));
        } else {
            panic!()
        }
    }

    #[test]
    fn meta_rules_with_unconstrained_list() {
        // edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].
        // El=Arg0, Q1=Arg1, Q2=Arg2
        // meta_vars = {El, Q1, Q2} = {0, 1, 2}
        // constrained_vars = {El} = {0}
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(
            tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].".into()).unwrap(),
        )
        .parse_all()
        .unwrap();

        let edge = SymbolDB::set_const("edge".into());
        let _q = SymbolDB::set_const("q".into());

        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((edge, 3)).unwrap() {
            let meta_rule = &clauses[0];
            // All three are meta_vars
            assert!(meta_rule.meta_var(0).unwrap()); // El
            assert!(meta_rule.meta_var(1).unwrap()); // Q1
            assert!(meta_rule.meta_var(2).unwrap()); // Q2
            // Only El is constrained
            assert!(meta_rule.constrained_var(0));  // El
            assert!(!meta_rule.constrained_var(1)); // Q1 — not constrained
            assert!(!meta_rule.constrained_var(2)); // Q2 — not constrained
        } else {
            panic!("Expected clauses for edge/3")
        }
    }

    #[test]
    fn meta_rules_list_only() {
        // edge(El,Q1,Q2):-q(Q1),q(Q2),[El,Q1,Q2].
        // El=Arg0, Q1=Arg1, Q2=Arg2
        // meta_vars = {El, Q1, Q2} = {0, 1, 2}
        // constrained_vars = {} (empty)
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(
            tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),[El,Q1,Q2].".into()).unwrap(),
        )
        .parse_all()
        .unwrap();

        let edge = SymbolDB::set_const("edge".into());
        let _q = SymbolDB::set_const("q".into());

        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((edge, 3)).unwrap() {
            let meta_rule = &clauses[0];
            // All three are meta_vars
            assert!(meta_rule.meta_var(0).unwrap()); // El
            assert!(meta_rule.meta_var(1).unwrap()); // Q1
            assert!(meta_rule.meta_var(2).unwrap()); // Q2
            // None are constrained
            assert!(!meta_rule.constrained_var(0));
            assert!(!meta_rule.constrained_var(1));
            assert!(!meta_rule.constrained_var(2));
        } else {
            panic!("Expected clauses for edge/3")
        }
    }

    #[test]
    fn meta_facts() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("Map([],[],X),{Map}.".into()).unwrap())
            .parse_all()
            .unwrap();

        execute_tree(facts, &mut heap, &mut pred_table);

        // Map is a variable, so we need to check via arity 3
        // The predicate symbol will be Arg 0 (the Map variable)
        // We need to find the clause differently since the predicate symbol is a variable
        
        // For a meta-fact with variable predicate, it gets indexed differently
        // Let's check the heap directly
        assert!(!heap.is_empty());
        
        // The head should be: (Func, 4), (Arg, 0), (ELis), (ELis), (Arg, 1)
        // where Arg 0 is the Map variable and Arg 1 is X
        assert_eq!(heap[0], (Tag::Func, 4));
        assert_eq!(heap[1], (Tag::Arg, 0)); // Map variable
        assert_eq!(heap[2].0, Tag::ELis);   // Empty list
        assert_eq!(heap[3].0, Tag::ELis);   // Empty list  
        assert_eq!(heap[4], (Tag::Arg, 1)); // X variable
    }
}
