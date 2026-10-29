//! AST execution: encodes parsed terms onto the heap and populates the predicate table.

use std::collections::HashMap;

use super::{
    build_tree::TreeClause,
    term::{Str, Term},
};
use crate::{
    heap::Heap,
    parser::{tokenise, ParserError, TokenStream},
    program::{
        clause::{Clause, MAX_ARG},
        predicate_table::PredicateTable,
    },
};

pub fn build_clause(
    literals: Vec<Term>,
    meta_vars: Option<(Vec<String>, Vec<String>)>,
    heap: &mut impl Heap,
    query: Option<usize>,
) -> Clause {
    let mut var_values = HashMap::new();

    //Pre order var_values so meta_rule instantiation arg ids are normalised
    if let Some((meta_vars, _)) = &meta_vars {
        let mut vars = Vec::new();
        for literal in &literals {
            literal.extract_vars(&mut vars);
        }
        for non_meta_var in vars.into_iter().filter(|var| !meta_vars.contains(var)) {
            let v = var_values.len();
            var_values.insert(non_meta_var, v);
        }
    }

    let literals: Vec<usize> = literals
        .into_iter()
        .map(|term| term.encode(heap, &mut var_values, query))
        .collect();

    assert!(
        var_values.len() <= MAX_ARG,
        "Clauses can not contain more than {MAX_ARG} variables."
    );

    let meta_vars = meta_vars.map(|vars| {
        (
            vars.0
                .into_iter()
                .map(|var| *var_values.get(&var).unwrap())
                .collect::<Vec<usize>>(),
            vars.1
                .into_iter()
                .map(|var| *var_values.get(&var).unwrap())
                .collect::<Vec<usize>>(),
        )
    });

    Clause::new(literals, meta_vars, var_values.len())
}

fn malformed(detail: impl Into<String>) -> ParserError {
    ParserError::MalformedMetaRule {
        detail: detail.into(),
    }
}

/// Extract variable names from a Term::Set
fn extract_var_names_from_set(term: Term) -> Result<Vec<String>, ParserError> {
    let Term::Str(Str::Set, set_terms) = term else {
        return Err(malformed("expected a set of meta variables, as in `{P,Q}`"));
    };
    set_terms
        .into_iter()
        .map(|term| match term {
            Term::Variable(symbol) => Ok(symbol),
            other => Err(malformed(format!(
                "a meta variable set may only contain variables, found `{other:?}`"
            ))),
        })
        .collect()
}

/// Extract variable names from a Term::List (must be a flat list with EmptyList tail)
fn extract_var_names_from_list(term: Term) -> Result<Vec<String>, ParserError> {
    let Term::List(list_terms, tail) = term else {
        return Err(malformed(
            "expected a list of unconstrained meta variables, as in `[Q,R]`",
        ));
    };
    if !matches!(*tail, Term::EmptyList) {
        return Err(malformed(
            "an unconstrained meta variable list may not have a tail",
        ));
    }
    list_terms
        .into_iter()
        .map(|term| match term {
            Term::Variable(symbol) => Ok(symbol),
            other => Err(malformed(format!(
                "an unconstrained meta variable list may only contain variables, \
                 found `{other:?}`"
            ))),
        })
        .collect()
}

/// Extract meta_vars and constrained_vars from a MetaRule's trailing terms.
///
/// Handles three cases:
/// - `...{P,Q,R}.` → meta_vars = {P,Q,R}, constrained_vars = None (defaults to all)
/// - `...{P},[Q1,Q2].` → meta_vars = {P,Q1,Q2}, constrained_vars = Some({P})
/// - `...[Q1,Q2].` → meta_vars = {Q1,Q2}, constrained_vars = Some({}) (empty)
fn extract_meta_rule_vars(
    terms: &mut Vec<Term>,
) -> Result<(Vec<String>, Vec<String>), ParserError> {
    let Some(last) = terms.pop() else {
        return Err(malformed("a meta rule must declare its meta variables"));
    };
    match last {
        // Case 1: last is {P,Q,R}
        Term::Str(Str::Set, _) => {
            let meta_vars = extract_var_names_from_set(last)?;
            Ok((meta_vars.clone(), meta_vars))
        }
        // Case 2 or 3: last is [Q1,Q2]
        Term::List(_, _) => {
            let unconstrained = extract_var_names_from_list(last)?;
            // Check if the new last element is a Set (Case 2: {P},[Q1,Q2])
            let constrained = if matches!(terms.last(), Some(Term::Str(Str::Set, _))) {
                let set = terms.pop().expect("just matched on the last element");
                extract_var_names_from_set(set)?
            } else {
                // Case 3: [Q1,Q2] only — no constrained vars
                Vec::new()
            };
            let mut meta_vars = constrained.clone();
            meta_vars.extend(unconstrained);
            Ok((meta_vars, constrained))
        }
        other => Err(malformed(format!(
            "a meta rule must end in a set or list of meta variables, found `{other:?}`"
        ))),
    }
}

/// Check what [`build_clause`] assumes about a meta rule before it encodes it.
///
/// `build_clause` looks every declared meta variable up in the map it builds
/// while encoding the literals, and indexes argument registers by the number
/// of variables. Both are invariants of the *source*, so they are checked
/// here, where the meta rule is still in hand and the failure can name it,
/// rather than surfacing as a panic from inside the encoder.
fn check_meta_rule_vars(literals: &[Term], meta_vars: &[String]) -> Result<(), ParserError> {
    let mut declared = Vec::new();
    for literal in literals {
        literal.extract_vars(&mut declared);
    }

    if declared.len() > MAX_ARG {
        return Err(malformed(format!(
            "a clause may not contain more than {MAX_ARG} variables, found {}",
            declared.len()
        )));
    }

    for meta_var in meta_vars {
        if !declared.contains(meta_var) {
            return Err(malformed(format!(
                "meta variable `{meta_var}` is declared but does not appear in the rule"
            )));
        }
    }
    Ok(())
}

/// Encode every parsed clause onto the heap and register it.
///
/// # Errors
///
/// Returns [`ParserError::MalformedMetaRule`] if a meta rule's trailing meta
/// variable declaration is missing, is not a set or list, contains anything
/// other than variables, or names a variable the rule does not use.
pub fn execute_tree(
    syntax_tree: Vec<TreeClause>,
    heap: &mut impl Heap,
    pred_table: &mut PredicateTable,
) -> Result<(), ParserError> {
    for clause in syntax_tree {
        let (literals, meta_vars) = match clause {
            TreeClause::Fact(term) => (vec![term], None),
            TreeClause::Rule(terms) => (terms, None),
            TreeClause::MetaRule(mut terms) => {
                let vars = extract_meta_rule_vars(&mut terms)?;
                check_meta_rule_vars(&terms, &vars.0)?;
                (terms, Some(vars))
            }
            TreeClause::MetaFact(head, meta_data) => {
                let meta_vars = extract_var_names_from_set(meta_data)?;
                let literals = vec![head];
                check_meta_rule_vars(&literals, &meta_vars)?;
                (literals, Some((meta_vars.clone(), meta_vars)))
            }
        };

        let clause = build_clause(literals, meta_vars, heap, None);
        let symbol_arity = heap.symbol_arity(clause[0]);
        pred_table
            .add_clause_to_predicate(clause, symbol_arity)
            .expect("a parsed clause never targets a built-in predicate function");
    }
    Ok(())
}

/// Testing helper
/// Build a single clause on heap without adding to a predicate table
pub(crate) fn _build_clause(heap: &mut impl Heap, clause: &str) -> Clause {
    let clause = TokenStream::new(tokenise(clause).unwrap())
        .parse_clause()
        .unwrap()
        .unwrap();
    match clause {
        TreeClause::Fact(term) => build_clause(vec![term], None, heap, None),
        TreeClause::Rule(terms) => build_clause(terms, None, heap, None),
        TreeClause::MetaRule(mut terms) => {
            let vars = extract_meta_rule_vars(&mut terms).unwrap();
            build_clause(terms, Some(vars), heap, None)
        }
        TreeClause::MetaFact(head, meta_data) => {
            let meta_vars = extract_var_names_from_set(meta_data).unwrap();
            build_clause(vec![head], Some((meta_vars.clone(), meta_vars)), heap, None)
        }
    }
}

#[cfg(test)]
mod malformed_meta_rule_tests {
    use super::{extract_meta_rule_vars, extract_var_names_from_list, extract_var_names_from_set};
    use crate::{
        app::App,
        parser::term::{Str, Term},
        Error, ParserError,
    };

    fn var(name: &str) -> Term {
        Term::Variable(name.to_string())
    }

    fn malformed_detail(error: &ParserError) -> &str {
        // `load_code` wraps parse errors with their source line.
        let error = match error {
            ParserError::AtLine { cause, .. } => &**cause,
            other => other,
        };
        match error {
            ParserError::MalformedMetaRule { detail } => detail,
            other => panic!("expected MalformedMetaRule, got {other:?}"),
        }
    }

    /// Source-level malformed declarations are rejected during parsing, before
    /// the AST reaches `execute_tree`. These cases are what a user actually
    /// types, so they are worth pinning even though the error is raised
    /// upstream of the code below.
    #[test]
    fn malformed_declarations_are_rejected_when_loading() {
        for (code, fragment) in [
            ("P(X):-Q(X),{P,bar}.", "existentially quantified variables"),
            ("P(X):-Q(X),{P},[bar].", "only contain variables"),
        ] {
            let Err(Error::Parser(error)) = App::default().load_code(code) else {
                panic!("`{code}` should not have loaded");
            };
            let detail = malformed_detail(&error);
            assert!(
                detail.contains(fragment),
                "detail for `{code}` was {detail:?}, expected it to mention {fragment:?}"
            );
        }
    }

    /// A trailing term that is not a set or list simply makes an ordinary
    /// rule, so these are not errors at all -- which is why the equivalent
    /// cases below have to be driven through the extraction helpers directly.
    #[test]
    fn a_non_declaration_trailing_term_is_an_ordinary_rule() {
        for code in ["P(X):-Q(X),foo.", "P(X):-Q(X),{P},[Q|R]."] {
            App::default()
                .load_code(code)
                .unwrap_or_else(|e| panic!("`{code}` should load as a plain rule, got {e:?}"));
        }
    }

    /// `execute_tree` is public, so these paths are reachable by a caller that
    /// builds its own AST. They used to `panic!`.
    #[test]
    fn declaration_must_be_a_set_or_list() {
        let mut terms = vec![var("P"), Term::Constant("foo".to_string())];
        let error = extract_meta_rule_vars(&mut terms).expect_err("foo is not a declaration");
        assert!(malformed_detail(&error).contains("set or list"));
    }

    #[test]
    fn declaration_must_be_present() {
        let error = extract_meta_rule_vars(&mut Vec::new()).expect_err("no declaration at all");
        assert!(malformed_detail(&error).contains("must declare"));
    }

    #[test]
    fn set_may_only_contain_variables() {
        let set = Term::Str(Str::Set, vec![var("P"), Term::Constant("bar".to_string())]);
        let error = extract_var_names_from_set(set).expect_err("bar is not a variable");
        assert!(malformed_detail(&error).contains("only contain variables"));
    }

    #[test]
    fn list_may_not_have_a_tail() {
        let list = Term::List(vec![var("Q")], Box::new(var("R")));
        let error = extract_var_names_from_list(list).expect_err("R is a tail");
        assert!(malformed_detail(&error).contains("may not have a tail"));
    }

    #[test]
    fn declared_meta_var_must_appear_in_the_rule() {
        let Err(Error::Parser(error)) = App::default().load_code("p(X):-q(X),{Z}.") else {
            panic!("a meta rule declaring an unused variable should not load");
        };
        assert!(malformed_detail(&error).contains("does not appear"));
    }

    /// The well-formed shapes must still load, so the checks above are not
    /// simply rejecting everything.
    #[test]
    fn well_formed_meta_rules_still_load() {
        for code in [
            "P(X):-Q(X),{P,Q}.",
            "P(X):-Q(X),R(X),{P,Q,R}.",
            "P(X):-Q(X),{P},[Q].",
            "P(X):-Q(X),[P,Q].",
        ] {
            App::default()
                .load_code(code)
                .unwrap_or_else(|e| panic!("`{code}` should load, got {e:?}"));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        heap::{Cell, SymbolDB, Tag},
        parser::execute_tree::execute_tree,
        program::predicate_table::{Predicate, PredicateTable},
    };

    use super::super::{build_tree::TokenStream, tokeniser::tokenise};

    #[test]
    fn facts() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(a,b).q(c).").unwrap())
            .parse_all()
            .unwrap();

        let [p, q, a, b, c] = ["p", "q", "a", "b", "c"].map(|s| SymbolDB::set_const(s));

        execute_tree(facts, &mut heap, &mut pred_table).unwrap();

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let fact = &clauses[0];
            assert_eq!(
                &heap[fact[0]..fact[0] + 4],
                &[(Tag::Comp, 3), (Tag::Con, p), (Tag::Con, a), (Tag::Con, b),]
            );
        } else {
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
            let fact = &clauses[0];
            assert_eq!(
                &heap[fact[0]..fact[0] + 3],
                &[(Tag::Comp, 2), (Tag::Con, q), (Tag::Con, c),]
            );
        } else {
            panic!()
        }
    }

    #[test]
    fn rules() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts =
            TokenStream::new(tokenise("p(X,Y):-q(X,a),q(Y,b). q(X):-r(X). q(X):-p(X).").unwrap())
                .parse_all()
                .unwrap();

        let [p, q, r, a, b] = ["p", "q", "r", "a", "b"].map(|s| SymbolDB::set_const(s));

        execute_tree(facts, &mut heap, &mut pred_table).unwrap();

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let rule = &clauses[0];
            assert_eq!(
                &heap[rule[0]..rule[0] + 4],
                &[(Tag::Comp, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 1),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 4],
                &[(Tag::Comp, 3), (Tag::Con, q), (Tag::Arg, 0), (Tag::Con, a),]
            );
            assert_eq!(
                &heap[rule[2]..rule[2] + 4],
                &[(Tag::Comp, 3), (Tag::Con, q), (Tag::Arg, 1), (Tag::Con, b),]
            );
        } else {
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
            let rule = &clauses[0];
            assert_eq!(
                &heap[rule[0]..rule[0] + 3],
                &[(Tag::Comp, 2), (Tag::Con, q), (Tag::Arg, 0),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 3],
                &[(Tag::Comp, 2), (Tag::Con, r), (Tag::Arg, 0),]
            );

            let rule = &clauses[1];
            assert_eq!(
                &heap[rule[0]..rule[0] + 3],
                &[(Tag::Comp, 2), (Tag::Con, q), (Tag::Arg, 0),]
            );
            assert_eq!(
                &heap[rule[1]..rule[1] + 3],
                &[(Tag::Comp, 2), (Tag::Con, p), (Tag::Arg, 0),]
            );
        } else {
            panic!()
        }
    }

    #[test]
    fn meta_rule_simple() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let clause = TokenStream::new(tokenise("P(X,Y):-Q(X),R(Y),{P,Q,R}.").unwrap())
            .parse_all()
            .unwrap();
        execute_tree(clause, &mut heap, &mut pred_table).unwrap();

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((0, 2)).unwrap() {
            let meta_rule = &clauses[0];
            assert_eq!(
                &heap[meta_rule[0]..meta_rule[0] + 4],
                &[(Tag::Comp, 3), (Tag::Arg, 2), (Tag::Arg, 0), (Tag::Arg, 1),]
            );
            assert_eq!(
                &heap[meta_rule[1]..meta_rule[1] + 3],
                &[(Tag::Comp, 2), (Tag::Arg, 3), (Tag::Arg, 0)]
            );
            assert_eq!(
                &heap[meta_rule[2]..meta_rule[2] + 3],
                &[(Tag::Comp, 2), (Tag::Arg, 4), (Tag::Arg, 1),]
            );
            assert!(meta_rule.meta_var(2).unwrap());
            assert!(meta_rule.meta_var(3).unwrap());
            assert!(meta_rule.meta_var(4).unwrap());
            assert!(meta_rule.constrained_var(2));
            assert!(meta_rule.constrained_var(3));
            assert!(meta_rule.constrained_var(4));
        } else {
            panic!()
        }
    }

    #[test]
    fn meta_rule_complex() {
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let clause = TokenStream::new(tokenise("p(X,Y):-Q(X,a),R(Y,b),{Q,R}.").unwrap())
            .parse_all()
            .unwrap();
        let [p, _q, _r, a, b] = ["p", "q", "r", "a", "b"].map(|s| SymbolDB::set_const(s));

        execute_tree(clause, &mut heap, &mut pred_table).unwrap();

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let meta_rule = &clauses[0];
            assert_eq!(
                &heap[meta_rule[0]..meta_rule[0] + 4],
                &[(Tag::Comp, 3), (Tag::Con, p), (Tag::Arg, 0), (Tag::Arg, 1),]
            );
            assert_eq!(
                &heap[meta_rule[1]..meta_rule[1] + 4],
                &[(Tag::Comp, 3), (Tag::Arg, 2), (Tag::Arg, 0), (Tag::Con, a),]
            );
            assert_eq!(
                &heap[meta_rule[2]..meta_rule[2] + 4],
                &[(Tag::Comp, 3), (Tag::Arg, 3), (Tag::Arg, 1), (Tag::Con, b),]
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
        let facts =
            TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].").unwrap())
                .parse_all()
                .unwrap();

        let edge = SymbolDB::set_const("edge");
        let _q = SymbolDB::set_const("q");

        execute_tree(facts, &mut heap, &mut pred_table).unwrap();

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((edge, 3)).unwrap() {
            let meta_rule = &clauses[0];
            // All three are meta_vars
            assert!(meta_rule.meta_var(0).unwrap()); // El
            assert!(meta_rule.meta_var(1).unwrap()); // Q1
            assert!(meta_rule.meta_var(2).unwrap()); // Q2
                                                     // Only El is constrained
            assert!(meta_rule.constrained_var(0)); // El
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
        let facts = TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),[El,Q1,Q2].").unwrap())
            .parse_all()
            .unwrap();

        let edge = SymbolDB::set_const("edge");
        let _q = SymbolDB::set_const("q");

        execute_tree(facts, &mut heap, &mut pred_table).unwrap();

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
        let facts = TokenStream::new(tokenise("Map([],[],X),{Map}.").unwrap())
            .parse_all()
            .unwrap();

        execute_tree(facts, &mut heap, &mut pred_table).unwrap();

        // Map is a variable, so we need to check via arity 3
        // The predicate symbol will be Arg 0 (the Map variable)
        // We need to find the clause differently since the predicate symbol is a variable

        // For a meta-fact with variable predicate, it gets indexed differently
        // Let's check the heap directly
        assert!(!heap.is_empty());

        // The head should be: (Func, 4), (Arg, 0), (ELis), (ELis), (Arg, 1)
        // where Arg 0 is the Map variable and Arg 1 is X
        assert_eq!(heap[0], (Tag::Comp, 4));
        assert_eq!(heap[1], (Tag::Arg, 1)); // Map variable
        assert_eq!(heap[2].0, Tag::ELis); // Empty list
        assert_eq!(heap[3].0, Tag::ELis); // Empty list
        assert_eq!(heap[4], (Tag::Arg, 0)); // X variable
    }
}
