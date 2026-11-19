//! AST execution: encodes parsed terms onto the heap and populates the predicate table.

use std::collections::HashMap;

use super::{
    build_tree::TreeClause,
    symmetry::{symmetries, Rule},
    term::{
        Str::*,
        Term::{self, *},
    },
};
use crate::{
    heap::Heap,
    parser::{tokenise, ParserError, TokenStream},
    program::{
        PredicateTable, {Clause, MAX_ARG},
    },
    Error,
};

pub(crate) fn build_clause(
    literals: Vec<Term>,
    meta_vars: Option<(Vec<String>, Vec<String>)>,
    heap: &mut impl Heap,
    query: bool,
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
            heap.observe_arg_count(v + 1);
        }
    }

    // Found on the terms, before encoding consumes them.
    let symmetry = meta_vars.as_ref().map(|(meta_vars, _)| {
        let rule = Rule {
            literals: &literals,
            meta_vars,
            namespaced: &[],
        };
        (rule.slots(), symmetries(&rule))
    });

    let literals: Vec<usize> = literals
        .into_iter()
        .map(|term| term.encode(heap, &mut var_values, query))
        .collect();

    assert!(
        var_values.len() <= MAX_ARG,
        "Clauses can not contain more than {MAX_ARG} variables."
    );

    // Record the width before anything can proof against it. A query's
    // variables live in the heap's register table proper, not the argument
    // window, so only a compiled clause counts.
    if !query {
        heap.observe_arg_count(var_values.len());
    }

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

    let clause = Clause::new(literals, meta_vars, var_values.len()).with_pred_vars(heap);
    let Some((slots, symmetries)) = symmetry else {
        return clause;
    };
    // The symmetries index the meta variables by order of first appearance,
    // which must be the order they were numbered in.
    let threshold = clause.meta_threshold().expect("a meta clause");
    assert!(
        slots
            .iter()
            .enumerate()
            .all(|(slot, var)| var_values[var] == threshold + slot),
        "meta variables {slots:?} are not numbered in order of first appearance"
    );
    clause.with_symmetries(&symmetries)
}

/// Namespace name to the predicate symbols a meta variable in it may take.
pub(crate) type Namespaces = HashMap<String, Vec<String>>;

fn malformed(detail: impl Into<String>) -> ParserError {
    ParserError::MalformedMetaRule {
        detail: detail.into(),
    }
}

/// Extract variable names from a Set
fn extract_var_names_from_set(term: Term) -> Result<Vec<String>, ParserError> {
    let Str(Set, set_terms) = term else {
        return Err(malformed("expected a set of meta variables, as in `{P,Q}`"));
    };
    set_terms
        .into_iter()
        .map(|term| match term {
            Variable(symbol) => Ok(symbol),
            other => Err(malformed(format!(
                "a meta variable set may only contain variables, found `{other:?}`"
            ))),
        })
        .collect()
}

/// Extract variable names from a List (must be a flat list with EmptyList tail)
fn extract_var_names_from_list(term: Term) -> Result<Vec<String>, ParserError> {
    let List(list_terms, tail) = term else {
        return Err(malformed(
            "expected a list of unconstrained meta variables, as in `[Q,R]`",
        ));
    };
    if !matches!(*tail, EmptyList) {
        return Err(malformed(
            "an unconstrained meta variable list may not have a tail",
        ));
    }
    list_terms
        .into_iter()
        .map(|term| match term {
            Variable(symbol) => Ok(symbol),
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
pub(super) fn extract_meta_rule_vars(
    terms: &mut Vec<Term>,
) -> Result<(Vec<String>, Vec<String>), ParserError> {
    let Some(last) = terms.pop() else {
        return Err(malformed("a meta rule must declare its meta variables"));
    };
    match last {
        // Case 1: last is {P,Q,R}
        Str(Set, _) => {
            let meta_vars = extract_var_names_from_set(last)?;
            Ok((meta_vars.clone(), meta_vars))
        }
        // Case 2 or 3: last is [Q1,Q2]
        List(_, _) => {
            let unconstrained = extract_var_names_from_list(last)?;
            // Check if the new last element is a Set (Case 2: {P},[Q1,Q2])
            let constrained = if matches!(terms.last(), Some(Str(Set, _))) {
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

/// Replace each `P:namespace` in a meta variable set or list with `P`,
/// returning the (variable, namespace) pairs removed.
pub(super) fn strip_namespaces(declaration: &mut Term) -> Vec<(String, String)> {
    let (Str(Set, terms) | List(terms, _)) = declaration else {
        return Vec::new();
    };
    let mut namespaced = Vec::new();
    for term in terms {
        let Str(Comp, parts) = term else { continue };
        if let [Constant(op), Variable(var), Constant(namespace)] = &parts[..] {
            if op == ":" {
                namespaced.push((var.clone(), namespace.clone()));
                *term = Variable(var.clone());
            }
        }
    }
    namespaced
}

/// True if `var` occurs anywhere but as the predicate symbol of a literal.
fn outside_predicate_position(term: &Term, var: &str) -> bool {
    match term {
        Variable(symbol) => symbol == var,
        Str(Comp, terms) => terms[1..]
            .iter()
            .any(|term| outside_predicate_position(term, var)),
        Str(_, terms) => terms
            .iter()
            .any(|term| outside_predicate_position(term, var)),
        List(head, tail) => {
            head.iter()
                .any(|term| outside_predicate_position(term, var))
                || outside_predicate_position(tail, var)
        }
        _ => false,
    }
}

fn substitute(term: &mut Term, var: &str, symbol: &str) {
    match term {
        Variable(name) if name == var => *term = Constant(symbol.to_string()),
        Str(_, terms) => terms
            .iter_mut()
            .for_each(|term| substitute(term, var, symbol)),
        List(head, tail) => {
            head.iter_mut()
                .for_each(|term| substitute(term, var, symbol));
            substitute(tail, var, symbol);
        }
        _ => (),
    }
}

type MetaVars = (Vec<String>, Vec<String>);

/// Compile a meta rule with namespaced meta variables into one variant per
/// assignment of namespace members to those variables.
///
/// Namespaced variables in the constrained set take pairwise different
/// members, as constrained meta variables may not take the same value.
/// Assignments that give the same clause with its body literals in another
/// order are compiled once.
fn expand_namespaces(
    literals: Vec<Term>,
    (meta_vars, constrained): MetaVars,
    namespaced: Vec<(String, String)>,
    namespaces: &Namespaces,
) -> crate::Result<Vec<(Vec<Term>, Option<MetaVars>)>> {
    if namespaced.is_empty() {
        return Ok(vec![(literals, Some((meta_vars, constrained)))]);
    }

    let mut members = Vec::with_capacity(namespaced.len());
    for (i, (var, namespace)) in namespaced.iter().enumerate() {
        if namespaced[..i].iter().any(|(earlier, _)| earlier == var) {
            return Err(malformed(format!(
                "meta variable `{var}` is given more than one namespace"
            ))
            .into());
        }
        if literals
            .iter()
            .any(|literal| outside_predicate_position(literal, var))
        {
            return Err(malformed(format!(
                "namespaced meta variable `{var}` may only be used as a predicate symbol"
            ))
            .into());
        }
        members.push(namespaces.get(namespace).ok_or_else(|| {
            Error::NameSpace(format!(
                "meta variable `{var}` uses the namespace `{namespace}`, which does not exist"
            ))
        })?);
    }

    let is_namespaced = |var: &String| namespaced.iter().any(|(name, _)| name == var);
    let is_constrained: Vec<bool> = namespaced
        .iter()
        .map(|(var, _)| constrained.contains(var))
        .collect();
    let remaining: MetaVars = (
        meta_vars
            .iter()
            .filter(|v| !is_namespaced(v))
            .cloned()
            .collect(),
        constrained
            .iter()
            .filter(|v| !is_namespaced(v))
            .cloned()
            .collect(),
    );
    // With no meta variables left a variant is an ordinary clause.
    let remaining = (!remaining.0.is_empty()).then_some(remaining);

    // Each symmetry of the rule as the namespaced variable every namespaced
    // variable becomes. An assignment and its image under one give the same
    // clause with its body reordered. A symmetry that swaps a constrained
    // variable with an unconstrained one is left out, as the two variants
    // would then be constrained differently.
    let rule = Rule {
        literals: &literals,
        meta_vars: &meta_vars,
        namespaced: &namespaced,
    };
    let slots = rule.slots();
    let position = |slot: &String| namespaced.iter().position(|(var, _)| var == slot);
    let swaps: Vec<Vec<usize>> = symmetries(&rule)
        .into_iter()
        .filter(|symmetry| {
            symmetry.iter().enumerate().all(|(from, &to)| {
                constrained.contains(&slots[from]) == constrained.contains(&slots[to as usize])
            })
        })
        .map(|symmetry| {
            namespaced
                .iter()
                .map(|(var, _)| {
                    let slot = slots.iter().position(|slot| slot == var).unwrap();
                    position(&slots[symmetry[slot] as usize])
                        .expect("a namespaced variable only becomes another")
                })
                .collect()
        })
        .collect();

    let mut variants = Vec::new();
    let mut choice = vec![0; namespaced.len()];
    if members.iter().any(|members| members.is_empty()) {
        return Ok(variants);
    }
    loop {
        let repeated = (0..choice.len()).any(|i| {
            is_constrained[i]
                && (0..i)
                    .any(|j| is_constrained[j] && members[i][choice[i]] == members[j][choice[j]])
        });
        // Of the assignments that give the same clause, keep the first.
        let reordering = swaps.iter().any(|swap| {
            let image = swap.iter().map(|&i| choice[i]);
            image.lt(choice.iter().copied())
        });
        if !repeated && !reordering {
            let mut variant = literals.clone();
            for (i, (var, _)) in namespaced.iter().enumerate() {
                for literal in &mut variant {
                    substitute(literal, var, &members[i][choice[i]]);
                }
            }
            variants.push((variant, remaining.clone()));
        }
        // Step to the next assignment, last variable fastest.
        let mut i = choice.len();
        loop {
            if i == 0 {
                return Ok(variants);
            }
            i -= 1;
            choice[i] += 1;
            if choice[i] < members[i].len() {
                break;
            }
            choice[i] = 0;
        }
    }
}

/// Encode every parsed clause onto the heap and register it.
///
/// A meta rule with namespaced meta variables (`{P,Q:name}`) is compiled
/// once for each assignment of the members of `namespaces[name]`.
///
/// # Errors
///
/// Returns [`ParserError::MalformedMetaRule`] if a meta rule's trailing meta
/// variable declaration is missing, is not a set or list, contains anything
/// other than variables, names a variable the rule does not use, or puts a
/// namespace on a variable that is not a predicate symbol.
///
/// Returns [`Error::NameSpace`] if a meta rule uses a namespace that does not
/// exist.
pub(crate) fn execute_tree(
    syntax_tree: Vec<TreeClause>,
    heap: &mut impl Heap,
    pred_table: &mut PredicateTable,
    namespaces: &Namespaces,
) -> crate::Result<()> {
    for clause in syntax_tree {
        let variants = match clause {
            TreeClause::Fact(term) => vec![(vec![term], None)],
            TreeClause::Rule(terms) => vec![(terms, None)],
            TreeClause::MetaRule(mut terms) => {
                let mut namespaced = Vec::new();
                // The declaration is the last term, or the last two: `{P},[Q]`.
                for declaration in terms.iter_mut().rev().take(2) {
                    namespaced.append(&mut strip_namespaces(declaration));
                }
                let vars = extract_meta_rule_vars(&mut terms)?;
                check_meta_rule_vars(&terms, &vars.0)?;
                expand_namespaces(terms, vars, namespaced, namespaces)?
            }
            TreeClause::MetaFact(head, mut meta_data) => {
                let namespaced = strip_namespaces(&mut meta_data);
                let meta_vars = extract_var_names_from_set(meta_data)?;
                let literals = vec![head];
                check_meta_rule_vars(&literals, &meta_vars)?;
                let vars = (meta_vars.clone(), meta_vars);
                expand_namespaces(literals, vars, namespaced, namespaces)?
            }
        };

        for (literals, meta_vars) in variants {
            let clause = build_clause(literals, meta_vars, heap, false);
            let symbol_arity = heap.symbol_arity(clause[0]);
            pred_table
                .add_clause_to_predicate(clause, symbol_arity)
                .expect("a parsed clause never targets a built-in predicate function");
        }
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
        TreeClause::Fact(term) => build_clause(vec![term], None, heap, false),
        TreeClause::Rule(terms) => build_clause(terms, None, heap, false),
        TreeClause::MetaRule(mut terms) => {
            let vars = extract_meta_rule_vars(&mut terms).unwrap();
            build_clause(terms, Some(vars), heap, false)
        }
        TreeClause::MetaFact(head, meta_data) => {
            let meta_vars = extract_var_names_from_set(meta_data).unwrap();
            build_clause(
                vec![head],
                Some((meta_vars.clone(), meta_vars)),
                heap,
                false,
            )
        }
    }
}

#[cfg(test)]
mod malformed_meta_rule_tests {

    use super::{extract_meta_rule_vars, extract_var_names_from_list, extract_var_names_from_set};
    use crate::{
        app::App,
        parser::term::{
            Str::*,
            Term::{self, *},
        },
        Error, ParserError,
    };

    fn var(name: &str) -> Term {
        Variable(name.to_string())
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
        let mut terms = vec![var("P"), Constant("foo".to_string())];
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
        let set = Str(Set, vec![var("P"), Constant("bar".to_string())]);
        let error = extract_var_names_from_set(set).expect_err("bar is not a variable");
        assert!(malformed_detail(&error).contains("only contain variables"));
    }

    #[test]
    fn list_may_not_have_a_tail() {
        let list = List(vec![var("Q")], Box::new(var("R")));
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
        heap::{Heap, ProgramHeap, Tag},
        parser::execute_tree::{execute_tree, Namespaces},
        program::{PredicateRef, PredicateTable},
    };

    use super::super::{build_tree::TokenStream, tokeniser::tokenise};

    #[test]
    fn facts() {
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(a,b).q(c).").unwrap())
            .parse_all()
            .unwrap();

        let [p, q, a, b, c] = ["p", "q", "a", "b", "c"].map(|s| heap.symbols().set_const(s));

        execute_tree(facts, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
            let fact = &clauses[0];
            assert_eq!(
                &heap[fact[0]..fact[0] + 4],
                &[(Tag::Comp, 3), (Tag::Con, p), (Tag::Con, a), (Tag::Con, b),]
            );
        } else {
            panic!()
        }

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let facts =
            TokenStream::new(tokenise("p(X,Y):-q(X,a),q(Y,b). q(X):-r(X). q(X):-p(X).").unwrap())
                .parse_all()
                .unwrap();

        let [p, q, r, a, b] = ["p", "q", "r", "a", "b"].map(|s| heap.symbols().set_const(s));

        execute_tree(facts, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
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

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((q, 1)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let clause = TokenStream::new(tokenise("P(X,Y):-Q(X),R(Y),{P,Q,R}.").unwrap())
            .parse_all()
            .unwrap();
        execute_tree(clause, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((0, 2)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let clause = TokenStream::new(tokenise("p(X,Y):-Q(X,a),R(Y,b),{Q,R}.").unwrap())
            .parse_all()
            .unwrap();
        let [p, _q, _r, a, b] = ["p", "q", "r", "a", "b"].map(|s| heap.symbols().set_const(s));

        execute_tree(clause, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((p, 2)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let facts =
            TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].").unwrap())
                .parse_all()
                .unwrap();

        let edge = heap.symbols().set_const("edge");
        let _q = heap.symbols().set_const("q");

        execute_tree(facts, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((edge, 3)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),[El,Q1,Q2].").unwrap())
            .parse_all()
            .unwrap();

        let edge = heap.symbols().set_const("edge");
        let _q = heap.symbols().set_const("q");

        execute_tree(facts, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

        if let PredicateRef::Clauses(clauses) = pred_table.get_predicate((edge, 3)).unwrap() {
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
        let mut heap = ProgramHeap::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("Map([],[],X),{Map}.").unwrap())
            .parse_all()
            .unwrap();

        execute_tree(facts, &mut heap, &mut pred_table, &Namespaces::new()).unwrap();

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

#[cfg(test)]
mod namespace_tests {
    use crate::{app::App, heap::Heap, Error, ParserError};

    fn comparators() -> App {
        App::default().namespace("cmp", ["lt", "gt", "le"]).unwrap()
    }

    /// The clauses of `p/1` as queries can see them: one per variant.
    fn count(app: App, code: &str, symbol: &str, arity: usize) -> usize {
        let app = app.load_code(code).unwrap();
        let symbol = app.prog_heap.symbols().set_const(symbol);
        app.predicate_table
            .get_predicate_clauses((symbol, arity))
            .map_or(0, |clauses| clauses.len())
    }

    #[test]
    fn one_variant_per_member() {
        assert_eq!(count(comparators(), "p(X):-Q(X,A),{Q:cmp,A}.", "p", 1), 3);
    }

    /// Variables whose literals cannot be swapped: every assignment is a
    /// different clause.
    #[test]
    fn constrained_variables_take_different_members() {
        let code = "p(X,Y):-Q(X,Z),R(Z,Y),{Q:cmp,R:cmp}.";
        assert_eq!(count(comparators(), code, "p", 2), 6);
    }

    #[test]
    fn unconstrained_variables_may_take_the_same_member() {
        let code = "p(X,Y):-Q(X,Z),R(Z,Y),[Q:cmp,R:cmp].";
        assert_eq!(count(comparators(), code, "p", 2), 9);
    }

    /// The clauses of `symbol/arity`, each with its symmetries.
    fn variants(code: &str, symbol: &str, arity: usize) -> Vec<Vec<Vec<u8>>> {
        let app = comparators().load_code(code).unwrap();
        let symbol = app.prog_heap.symbols().set_const(symbol);
        app.predicate_table
            .get_predicate_clauses((symbol, arity))
            .unwrap_or_default()
            .iter()
            .map(|clause| clause.symmetries().map(<[u8]>::to_vec).collect())
            .collect()
    }

    /// `Q` and `R` swap, taking `A` and `B` with them, so `lt,gt` and
    /// `gt,lt` are one clause: 3 pairs rather than 6.
    #[test]
    fn a_reordered_assignment_is_compiled_once() {
        let code = "p(X):-Q(X,A),R(X,B),{Q:cmp,R:cmp,A,B}.";
        let variants = variants(code, "p", 1);
        assert_eq!(variants.len(), 3);
        // The members differ, so no variant has a symmetry left.
        assert!(variants.iter().all(|symmetries| symmetries.is_empty()));
    }

    /// Unconstrained, the 3 pairs are joined by the 3 assignments of one
    /// member to both. Those keep the symmetry between `A` and `B`.
    #[test]
    fn a_variant_with_a_member_twice_is_still_symmetric() {
        let code = "p(X):-Q(X,A),R(X,B),{A,B},[Q:cmp,R:cmp].";
        let variants = variants(code, "p", 1);
        assert_eq!(variants.len(), 6);
        // Slots of a variant: A, B.
        let symmetric = variants.iter().filter(|s| **s == [[1, 0]]).count();
        assert_eq!(symmetric, 3);
    }

    #[test]
    fn three_variables_alike_give_one_variant_per_set_of_members() {
        let code = "p(X):-Q(X),R(X),S(X),{Q:cmp,R:cmp,S:cmp}.";
        assert_eq!(variants(code, "p", 1).len(), 1);
        let code = "p(X):-Q(X),R(X),S(X),[Q:cmp,R:cmp,S:cmp].";
        // Multisets of 3 from 3 members.
        assert_eq!(variants(code, "p", 1).len(), 10);
    }

    /// A namespaced variable never swaps with one outside the namespace, so
    /// nothing is dropped. (`R` may still take a member of `cmp` during a
    /// proof; that reordering is not caught here.)
    #[test]
    fn a_namespaced_and_a_free_variable_do_not_swap() {
        let code = "p(X):-Q(X),R(X),{Q:cmp,R}.";
        let variants = variants(code, "p", 1);
        assert_eq!(variants.len(), 3);
        assert!(variants.iter().all(|symmetries| symmetries.is_empty()));
    }

    /// The namespaced pair and the free pair swap separately. Expansion
    /// uses the first, and each variant keeps the second.
    #[test]
    fn a_symmetry_between_free_variables_survives_expansion() {
        let code = "p(X):-C(X),D(X),Q(X),R(X),{C:cmp,D:cmp,Q,R}.";
        let variants = variants(code, "p", 1);
        assert_eq!(variants.len(), 3);
        // Slots of a variant: Q, R.
        assert!(variants.iter().all(|symmetries| *symmetries == [[1, 0]]));
    }

    /// `C` and `D` swap only if the free `S` and `T` swap with them.
    #[test]
    fn a_swap_may_carry_free_variables_with_it() {
        let code = "p(X):-C(X,A),D(X,B),S(A),T(B),{C:cmp,D:cmp,S,T}.";
        assert_eq!(variants(code, "p", 1).len(), 3);
        // With `t` a constant they cannot, so no assignment is dropped.
        let code = "p(X):-C(X,A),D(X,B),S(A),t(B),{C:cmp,D:cmp,S}.";
        assert_eq!(variants(code, "p", 1).len(), 6);
    }

    /// Swapping a constrained variable with an unconstrained one would give
    /// variants constrained differently, so both orders are kept.
    #[test]
    fn a_swap_across_the_constrained_set_is_not_used() {
        let code = "p(X):-Q(X),R(X),{Q:cmp},[R:cmp].";
        assert_eq!(variants(code, "p", 1).len(), 9);
    }

    /// Two namespaces with the same members are still different kinds.
    #[test]
    fn variables_of_different_namespaces_do_not_swap() {
        let app = comparators()
            .namespace("other", ["lt", "gt", "le"])
            .unwrap();
        let app = app.load_code("p(X):-Q(X),R(X),{Q:cmp,R:other}.").unwrap();
        let symbol = app.prog_heap.symbols().set_const("p");
        let clauses = app.predicate_table.get_predicate_clauses((symbol, 1));
        assert_eq!(clauses.unwrap().len(), 6);
    }

    #[test]
    fn a_variant_behaves_as_the_clause_written_out() {
        let app = App::default()
            .namespace("cmp", ["lt", "gt"])
            .unwrap()
            .load_code("lt(1,2). gt(2,1). p(X,Y):-Q(X,Y),{Q:cmp}.")
            .unwrap();
        for (query, expected) in [("p(1,2).", true), ("p(2,1).", true), ("p(1,1).", false)] {
            let mut session = app.query_session(query).unwrap();
            assert_eq!(session.next().is_some(), expected, "{query}");
        }
    }

    #[test]
    fn an_unknown_namespace_is_an_error() {
        let result = comparators().load_code("p(X):-Q(X),{Q:other}.");
        assert!(matches!(result, Err(Error::NameSpace(_))));
    }

    #[test]
    fn a_namespace_cannot_be_given_twice() {
        let result = comparators().namespace("cmp", ["eq"]);
        assert!(matches!(result, Err(Error::NameSpace(_))));
    }

    #[test]
    fn misuse_is_an_error() {
        for (code, fragment) in [
            (
                "p(X):-q(X,Q),Q(X),{Q:cmp}.",
                "only be used as a predicate symbol",
            ),
            ("p(X):-Q(X),{Q:cmp,Q:cmp}.", "more than one namespace"),
        ] {
            let Err(Error::Parser(error)) = comparators().load_code(code) else {
                panic!("`{code}` should not have loaded");
            };
            let error = match &error {
                ParserError::AtLine { cause, .. } => &**cause,
                other => other,
            };
            assert!(error.to_string().contains(fragment), "{code}: {error}");
        }
    }
}

#[cfg(test)]
mod symmetry_tests {
    use super::_build_clause;
    use crate::{heap::ProgramHeap, program::MetaBox};

    fn symmetries(code: &str) -> Vec<Vec<u8>> {
        let clause = _build_clause(&mut ProgramHeap::new(), code);
        clause.symmetries().map(<[u8]>::to_vec).collect()
    }

    #[test]
    fn a_compiled_meta_clause_carries_its_symmetries() {
        assert_eq!(symmetries("P(X):-Q(X),R(X),{P,Q,R}."), [[0, 2, 1]]);
        assert_eq!(
            symmetries("P(X,Y,Z):-C(Z,A),D(Z,B),Q(X,Y),{P,Q,C,D,A,B}."),
            [[0, 3, 4, 1, 2, 5]]
        );
        assert_eq!(symmetries("P(X):-Q(X),R(X),S(X),{P,Q,R,S}.").len(), 5);
    }

    #[test]
    fn other_clauses_have_none() {
        assert!(symmetries("P(X,Y):-Q(X,Z),R(Z,Y),{P,Q,R}.").is_empty());
        assert!(symmetries("p(X):-q(X),r(X).").is_empty());
    }

    /// The meta data and symmetries are one allocation behind one word, and
    /// a clause without them pays nothing more.
    #[test]
    fn meta_data_is_one_word() {
        let word = std::mem::size_of::<usize>();
        assert_eq!(std::mem::size_of::<Option<MetaBox>>(), word);
    }
}
