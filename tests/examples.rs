// Broad test on example files to prove working state of application
use prolog2::{
    app::{App, Solution},
    ResolutionConfig,
};

pub(crate) fn contains_clause(solution: &Solution, clause: &str) -> bool {
    solution
        .hypothesis
        .lines()
        .any(|h_clause| h_clause == clause)
}

pub(crate) fn matching_hypothesis(solution: &Solution, expected_h: &[&str]) -> bool {
    if solution.hypothesis.chars().filter(|c| *c == '\n').count() != expected_h.len() {
        return false;
    }
    for clause in expected_h {
        if !contains_clause(solution, clause) {
            return false;
        }
    }
    true
}

pub(crate) fn hypothesis_exists(solutions: &[Solution], expected_h: &[&str]) {
    if !solutions
        .iter()
        .any(|solution| matching_hypothesis(solution, expected_h))
    {
        panic!(
            "Solutions: \n {} \ndid not contain expected hypothesis:\n{}",
            solutions
                .iter()
                .map(|sol| format!("{}\n------------------", sol.hypothesis))
                .collect::<String>(),
            expected_h
                .iter()
                .map(|clause| [clause, "\n"].concat())
                .collect::<String>()
        )
    }
}

pub(crate) fn test_solutions(app: App, expected_hypotheses: &[&[&str]]) {
    let mut i = 0;
    let solutions: Vec<Solution> = app
        .query_session_from_examples()
        .unwrap()
        .inspect(|solution| {
            println!("Hypthesis {i}:\n{}\n", solution.hypothesis);
            i += 1;
        })
        .collect();
    for expected_h in expected_hypotheses {
        hypothesis_exists(&solutions, expected_h);
    }
}

/// The identifiers and the text between them, in order: `(text, is_identifier)`.
fn tokens(text: &str) -> Vec<(&str, bool)> {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut tokens = Vec::new();
    let mut start = 0;
    let mut chars = text.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        let ends = chars
            .peek()
            .is_none_or(|&(_, next)| is_ident(next) != is_ident(c));
        if ends {
            let end = i + c.len_utf8();
            tokens.push((&text[start..end], is_ident(c)));
            start = end;
        }
    }
    tokens
}

/// Whether `name` is one coined for an invented predicate: `pred_<n>`.
fn invented(name: &str) -> bool {
    name.strip_prefix("pred_")
        .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
}

fn variable(name: &str) -> bool {
    name.starts_with(|c: char| c.is_uppercase() || c == '_')
}

/// `text` with each identifier put through `rename`.
fn renamed(text: &str, mut rename: impl FnMut(&str) -> String) -> String {
    tokens(text)
        .into_iter()
        .map(|(token, is_ident)| match is_ident {
            true => rename(token),
            false => token.to_string(),
        })
        .collect()
}

/// A clause in a form that does not depend on the order of its body
/// literals or on what its variables are called.
///
/// The body literals are sorted with their variables blanked, then the
/// variables are numbered in the order they come.
fn canonical_clause(clause: &str) -> String {
    let clause = clause.trim().trim_end_matches('.');
    let (head, body) = clause.split_once(":-").unwrap_or((clause, ""));

    // Body literals, split at the commas outside any brackets.
    let mut literals: Vec<&str> = Vec::new();
    let (mut depth, mut start) = (0, 0);
    for (i, c) in body.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                literals.push(&body[start..i]);
                start = i + 1;
            }
            _ => (),
        }
    }
    if !body[start..].is_empty() {
        literals.push(&body[start..]);
    }
    let blanked = |literal: &str| {
        renamed(literal, |name| match variable(name) {
            true => "_".to_string(),
            false => name.to_string(),
        })
    };
    literals.sort_by_key(|literal| blanked(literal));

    let ordered = format!("{head}:-{}", literals.join(","));
    let mut variables: Vec<String> = Vec::new();
    renamed(&ordered, |name| {
        if !variable(name) {
            return name.to_string();
        }
        let n = variables
            .iter()
            .position(|seen| seen == name)
            .unwrap_or_else(|| {
                variables.push(name.to_string());
                variables.len() - 1
            });
        format!("V{n}")
    })
}

/// The invented predicate names in `clauses`, each once, in order.
fn invented_names<'a>(clauses: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut names = Vec::new();
    for clause in clauses {
        for (token, is_ident) in tokens(clause) {
            if is_ident && invented(token) && !names.contains(&token) {
                names.push(token);
            }
        }
    }
    names
}

/// Every order of `items`.
fn orders<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut all = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let first = rest.remove(i);
        for mut order in orders(&rest) {
            order.insert(0, first.clone());
            all.push(order);
        }
    }
    all
}

/// Whether `hypothesis`, one clause to a line, is `expected_h`.
///
/// A parallel run names invented predicates and orders body literals as
/// its threads happen to finish, so the two are compared whatever the
/// invented predicates are called, whatever order the clauses and their
/// body literals come in, and whatever the variables are called.
pub(crate) fn matching_parallel_hypothesis(hypothesis: &str, expected_h: &[&str]) -> bool {
    let clauses: Vec<&str> = hypothesis.lines().filter(|line| !line.is_empty()).collect();
    let (names, expected_names) = (
        invented_names(clauses.iter().copied()),
        invented_names(expected_h.iter().copied()),
    );
    if clauses.len() != expected_h.len() || names.len() != expected_names.len() {
        return false;
    }

    let canonical = |clauses: Vec<String>| {
        let mut clauses: Vec<String> = clauses.iter().map(|c| canonical_clause(c)).collect();
        clauses.sort();
        clauses
    };
    let expected = canonical(expected_h.iter().map(|clause| clause.to_string()).collect());
    // Try each way of taking its invented names for the expected ones.
    orders(&expected_names).into_iter().any(|expected_names| {
        let as_expected = |name: &str| match names.iter().position(|n| *n == name) {
            Some(i) => expected_names[i].to_string(),
            None => name.to_string(),
        };
        canonical(
            clauses
                .iter()
                .map(|clause| renamed(clause, as_expected))
                .collect(),
        ) == expected
    })
}

/// Learn from the app's examples with the parallel learner, and check that
/// each of `expected_hypotheses` is among the hypotheses it returns.
///
/// See [`matching_parallel_hypothesis`] for what counts as the same.
pub(crate) fn test_parallel_solutions(mut app: App, expected_hypotheses: &[&[&str]]) {
    let hypotheses = app
        .run_parallel()
        .expect("the parallel learner found no hypothesis");
    for (i, hypothesis) in hypotheses.iter().enumerate() {
        println!("Hypothesis {i}:\n{hypothesis}\n");
    }
    for expected_h in expected_hypotheses {
        if !hypotheses
            .iter()
            .any(|hypothesis| matching_parallel_hypothesis(hypothesis, expected_h))
        {
            panic!(
                "Hypotheses:\n{}\ndid not contain expected hypothesis:\n{}",
                hypotheses
                    .iter()
                    .map(|hypothesis| format!("{hypothesis}------------------\n"))
                    .collect::<String>(),
                expected_h
                    .iter()
                    .map(|clause| [clause, "\n"].concat())
                    .collect::<String>()
            )
        }
    }
}

#[test]
fn parallel_hypotheses_match_whatever_the_names_and_order() {
    let found = "pred_5(A):-closed(A),short(A).\ne(A):-has_car(A,B),pred_5(B).\n";
    assert!(matching_parallel_hypothesis(
        found,
        &[
            "e(X):-pred_1(Y),has_car(X,Y).",
            "pred_1(A):-short(A),closed(A)."
        ]
    ));
    // A different body, a missing clause, or another predicate is no match.
    assert!(!matching_parallel_hypothesis(
        found,
        &[
            "e(A):-has_car(A,B),pred_1(B).",
            "pred_1(A):-short(A),long(A)."
        ]
    ));
    assert!(!matching_parallel_hypothesis(
        found,
        &["e(A):-has_car(A,B),pred_1(B)."]
    ));
    assert!(!matching_parallel_hypothesis(
        found,
        &[
            "e(A):-has_car(A,B),pred_1(A).",
            "pred_1(A):-short(A),closed(A)."
        ]
    ));
    // Two invented predicates are matched up either way round.
    assert!(matching_parallel_hypothesis(
        "p(A):-pred_2(A).\npred_2(A):-pred_7(A).\npred_7(A):-q(A).\n",
        &[
            "p(A):-pred_1(A).",
            "pred_2(A):-q(A).",
            "pred_1(A):-pred_2(A)."
        ]
    ));
}

#[test]
fn ancestor() {
    const H1: &[&str] = &[
        "ancestor(A,B):-dad(A,C),ancestor(C,B).",
        "ancestor(A,B):-dad(A,B).",
        "ancestor(A,B):-mum(A,C),ancestor(C,B).",
        "ancestor(A,B):-mum(A,B).",
    ];

    const H2: &[&str] = &[
        "ancestor(A,B):-pred_1(A,C),ancestor(C,B).",
        "ancestor(A,B):-pred_1(A,B).",
        "pred_1(A,B):-dad(A,B).",
        "pred_1(A,B):-mum(A,B).",
    ];

    let app = App::from_config_json("examples/ancestor/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

#[test]
fn map() {
    let app = App::from_config_json("examples/map/config.json").expect("failed to load config");
    // Grounded Double
    let solutions: Vec<Solution> = app
        .query_session("map([1,2,3],[2,4,6],double).")
        .unwrap()
        .collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
    // Bind Double
    let solutions: Vec<Solution> = app
        .query_session("map([1,2,3],[2,4,6],X).")
        .unwrap()
        .collect();
    assert!(solutions.iter().any(|solution| solution
        .bindings
        .iter()
        .any(|binding| *binding.0 == *"X" && binding.1 == "double")));
}

#[test]
fn odd_even() {
    const H1: &[&str] = &[
        "even(A):-prev(A,B),pred_1(B).",
        "pred_1(A):-prev(A,B),even(B).",
        "pred_1(A):-prev(A,B),zero(B).",
    ];

    const H2: &[&str] = &[
        "even(A):-prev(A,B),pred_1(B).",
        "pred_1(A):-prev(A,B),even(B).",
        "even(A):-zero(A).",
    ];

    let app = App::from_config_json("examples/odd_even/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

#[test]
fn learn_map_double() {
    const H1: &[&str] = &[
        "map_double([A|B],[C|D],double):-double(A,C),map_double(B,D,double).",
        "double(A,B):-add(A,A,B).",
        "map_double([],[],A).",
    ];
    let app = App::from_config_json("examples/map/learn_config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1]);
}

#[test]
fn trains() {
    const H1: &[&str] = &[
        "e(A):-has_car(A,B),pred_1(B).",
        "pred_1(A):-closed(A),short(A).",
    ];
    const H2: &[&str] = &[
        "e(A):-pred_1(A,B),closed(B).",
        "pred_1(A,B):-has_car(A,B),short(B).",
    ];
    const H3: &[&str] = &[
        "e(A):-pred_1(A,B),short(B).",
        "pred_1(A,B):-has_car(A,B),closed(B).",
    ];
    let app = App::from_config_json("examples/trains/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2, H3]);
}

#[test]
fn fsm_parity() {
    const H1: &[&str] = &[
        "edge(0,even,even):-q(even),q(even).",
        "edge(1,even,odd):-q(even),q(odd).",
        "edge(0,odd,odd):-q(odd),q(odd).",
        "edge(1,odd,even):-q(odd),q(even).",
    ];
    let app = App::from_config_json("examples/parity/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1]);
}

// ── Parallel learner tests ──

#[test]
fn parallel_robots() {
    let app = App::from_config_json("examples/robots/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    // No one hypothesis is expected, only that some are found.
    test_parallel_solutions(app, &[]);
}

// Regression test for the molecules example.
//
// This example uses a negative example (`phenolic(benzene)`), which drives
// negation-as-failure (`not/1`) during top program construction. The inner
// proof spawned by `not/1` runs on the *shared* heap and used to leave
// forward bindings (old_var -> freshly_built_high_addr) behind; a later heap
// truncation by the outer proof then dangled those refs and panicked in
// `deref_addr`. This test ensures top program construction completes and
// produces a hypothesis without panicking.
// #[test]
// fn top_prog_molecules_not() {
//     let mut app = App::from_config_json("examples/molecules/phenolic.json")
//         .expect("failed to load molecules setup")
//         .auto(true);
//     let result = app.run_top_prog();
//     assert!(
//         result.contains("phenolic("),
//         "expected a phenolic hypothesis, got:\n{result}"
//     );
// }

#[test]
fn parallel_trains() {
    let app = App::from_config_json("examples/trains/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    test_parallel_solutions(
        app,
        &[&[
            "e(A):-has_car(A,B),pred_1(B).",
            "pred_1(A):-short(A),closed(A).",
        ]],
    );
}

const COLREG_CONF: ResolutionConfig = ResolutionConfig {
    max_depth: 5,
    max_clause: 2,
    debug: false,
    protect_h_preds: true,
};

#[test]
fn cpa_side() {
    let mut app = App::from_config_json("examples/colreg/cpa_side.json")
        .expect("failed to load config")
        .resolution(|_| COLREG_CONF);
    let _result = app.run_parallel();
}

#[test]
fn turn() {
    let mut app = App::from_config_json("examples/colreg/turn.json")
        .expect("failed to load config")
        .resolution(|_| COLREG_CONF);
    let _result = app.run_parallel();
}

#[test]
fn avoid() {
    let mut app = App::from_config_json("examples/colreg/avoid.json")
        .expect("failed to load config")
        .resolution(|_| COLREG_CONF);
    let _result = app.run_parallel();
}

#[test]
fn resume() {
    let mut app = App::from_config_json("examples/colreg/resume.json")
        .expect("failed to load config")
        .resolution(|_| COLREG_CONF);
    let _result = app.run_parallel();
}
