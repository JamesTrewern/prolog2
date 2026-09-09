// Broad test on example files to prove working state of application
use std::path::Path;

use crate::app::{App, Config, Examples, Solution};

pub fn contains_clause(solution: &Solution, clause: &str) -> bool {
    solution
        .hypothesis
        .lines()
        .any(|h_clause| h_clause == clause)
}

pub fn matching_hypothesis(solution: &Solution, expected_h: &[&str]) -> bool {
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

pub fn hypothesis_exists(solutions: &[Solution], expected_h: &[&str]) {
    if !solutions
        .iter()
        .any(|solution| matching_hypothesis(solution, expected_h))
    {
        panic!(
            "Solutions did not contain expected hypothesis:\n{}",
            expected_h
                .iter()
                .map(|clause| [clause, "\n"].concat())
                .collect::<String>()
        )
    }
}

pub fn test_solutions(app: App, expected_hypotheses: &[&[&str]]) {
    let mut i = 0;
    let solutions: Vec<Solution> = app
        .query_session_from_examples()
        .unwrap()
        .inspect(|solution| {println!("Hypthesis {i}:\n{}\n", solution.hypothesis); i+=1;})
        .collect();
    for expected_h in expected_hypotheses {
        hypothesis_exists(&solutions, expected_h);
    }
}

#[test]
fn ancestor() {
    const H1: &[&str] = &[
        "ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).",
        "ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_1).",
        "ancestor(Arg_0,Arg_1):-mum(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).",
        "ancestor(Arg_0,Arg_1):-mum(Arg_0,Arg_1).",
    ];

    const H2: &[&str] = &[
        "ancestor(Arg_0,Arg_1):-pred_1(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).",
        "ancestor(Arg_0,Arg_1):-pred_1(Arg_0,Arg_1).",
        "pred_1(Arg_0,Arg_1):-dad(Arg_0,Arg_1).",
        "pred_1(Arg_0,Arg_1):-mum(Arg_0,Arg_1).",
    ];

    let app = App::from_setup_json("examples/ancestor/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

// ── protect_h_preds ──────────────────────────────────────────────────────
//
// The ancestor example is the sharpest test of this flag. `dad` and `mum` are
// background predicates, so a hypothesis clause headed by either can only have
// arisen from an invented predicate being captured by a background symbol.

/// The head predicate of a rendered clause: `"dad"` from `"dad(A,B):-...".`
fn head_symbol(clause: &str) -> &str {
    clause.split('(').next().unwrap_or(clause)
}

/// Every clause across every solution that redefines a background predicate.
fn background_redefinitions(solutions: &[Solution]) -> Vec<String> {
    solutions
        .iter()
        .flat_map(|solution| solution.hypothesis.lines())
        .filter(|clause| matches!(head_symbol(clause), "dad" | "mum"))
        .map(str::to_string)
        .collect()
}

fn ancestor_solutions(protect_h_preds: bool) -> Vec<Solution> {
    let app = App::from_setup_json("examples/ancestor/config.json")
        .expect("failed to load config")
        .auto(true);
    let config = Config {
        protect_h_preds,
        ..app.config
    };
    app.config(config)
        .query_session_from_examples()
        .unwrap()
        .collect()
}

// ── hypothesis reuse across examples ─────────────────────────────────────
//
// The target predicate has no background definition, so goals on it reach the
// unknown-symbol branch of choice gathering, which offers the whole
// hypothesis. That is what lets a hypothesis learned while discharging the
// first example or two discharge the rest: once `max_clause` is reached no
// further clauses may be added, so the remaining goals can only succeed by
// re-using what is already there. They are, in effect, a test set.
//
// `dad` alone is declared as a body predicate, so the only hypothesis that can
// cover every example is the two-clause transitive closure of `dad`. The
// paternal line in family.pl is jim -> ken -> adam -> james, with ken also
// fathering saul and kelly, adam also fathering luke, and chris fathering
// tami.

/// Build a paternal-ancestry learner over `examples/ancestor/family.pl`.
///
/// The target is named `p_ancestor` so that it is an unknown symbol with no
/// background clauses, exactly as a target predicate is.
fn paternal_ancestor_app(pos: &[&str], neg: &[&str], max_clause: usize) -> App {
    App::default()
        .config(Config {
            max_depth: 15,
            max_clause,
            max_pred: 1,
            debug: false,
            protect_h_preds: true,
        })
        .load_file(Path::new("examples/ancestor/family.pl"))
        .expect("failed to load family.pl")
        // Declared after loading, as `App::from_setup_json` does: the
        // predicate must exist in the table before it can be marked as a body
        // predicate.
        .add_body_predicates(["dad/2"])
        .expect("failed to declare body predicates")
        .examples(Examples {
            pos: pos.iter().map(|s| s.to_string()).collect(),
            neg: neg.iter().map(|s| s.to_string()).collect(),
        })
        .auto(true)
}

#[test]
fn hypothesis_clauses_are_reused_across_repeated_examples() {
    // Five positive examples of one target, but only two clauses allowed. The
    // first two goals exhaust the clause budget; the last three can only
    // succeed by re-using those clauses.
    const EXPECTED: &[&str] = &[
        "p_ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_1).",
        "p_ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_2),p_ancestor(Arg_2,Arg_1).",
    ];

    let app = paternal_ancestor_app(
        &[
            "p_ancestor(jim,ken)",    // base case
            "p_ancestor(chris,tami)", // base case again, re-using clause one
            "p_ancestor(jim,adam)",   // one recursive step
            "p_ancestor(ken,luke)",   // two steps: ken -> adam -> luke
            "p_ancestor(jim,james)",  // three steps
        ],
        &[],
        2,
    );

    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(
        !solutions.is_empty(),
        "five examples could not be covered by a two-clause hypothesis, so \
         clauses learned for the early goals were not re-used by the later ones"
    );
    hypothesis_exists(&solutions, EXPECTED);
}

#[test]
fn reuse_is_what_makes_the_clause_budget_sufficient() {
    // The counterpart to the test above: with only one clause allowed, the
    // recursive examples cannot be covered and the search must fail. This
    // pins the budget as load-bearing, so the test above is really showing
    // reuse rather than a budget large enough to learn each example
    // separately.
    let app = paternal_ancestor_app(
        &[
            "p_ancestor(jim,ken)",
            "p_ancestor(jim,adam)",
            "p_ancestor(jim,james)",
        ],
        &[],
        1,
    );
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(
        solutions.is_empty(),
        "a single clause should not cover recursive ancestry"
    );
}

#[test]
#[ignore = "negation as failure is blocked on predicate_modules::helpers::resolve, \
            which is todo!() pending the flat-terms migration; \
            meta_predicates::not calls it and panics"]
fn negative_examples_are_ruled_out_against_the_learned_hypothesis() {
    // Negative examples are wrapped in `not(...)`, so they succeed only when
    // the goal is exhaustively unprovable from the hypothesis plus background
    // knowledge, with learning off. None of these pairs lies in the transitive
    // closure of `dad`: james -> jim reverses the line, tami is reached only
    // by `mum`, and no paternal path runs from ken to tami.
    const EXPECTED: &[&str] = &[
        "p_ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_1).",
        "p_ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_2),p_ancestor(Arg_2,Arg_1).",
    ];

    let app = paternal_ancestor_app(
        &["p_ancestor(jim,ken)", "p_ancestor(jim,james)"],
        &[
            "p_ancestor(james,jim)",
            "p_ancestor(tami,james)",
            "p_ancestor(ken,tami)",
        ],
        2,
    );

    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(
        !solutions.is_empty(),
        "the correct hypothesis should satisfy the negative examples too"
    );
    hypothesis_exists(&solutions, EXPECTED);
}

#[test]
#[ignore = "negation as failure is blocked on predicate_modules::helpers::resolve, \
            which is todo!() pending the flat-terms migration; \
            meta_predicates::not calls it and panics"]
fn a_negative_example_that_the_hypothesis_entails_is_rejected() {
    // ken -> adam -> james is a paternal path, so any hypothesis covering the
    // positive examples also proves this negative one. Every candidate must
    // therefore be rejected and the search must fail outright. Without a
    // working negation-as-failure search this would wrongly succeed.
    let app = paternal_ancestor_app(
        &["p_ancestor(jim,ken)", "p_ancestor(jim,james)"],
        &["p_ancestor(ken,james)"],
        2,
    );
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(
        solutions.is_empty(),
        "a negative example entailed by the hypothesis must rule it out"
    );
}

#[test]
fn protect_h_preds_defaults_to_true_when_absent_from_setup_file() {
    // examples/ancestor/config.json deliberately omits the key, so this also
    // pins the behaviour of every existing setup file in the repository.
    let app = App::from_setup_json("examples/ancestor/config.json").expect("failed to load config");
    assert!(app.config.protect_h_preds);
    assert!(Config::default().protect_h_preds);
}

#[test]
fn protect_h_preds_is_read_when_present() {
    let with = |value: &str| -> Config {
        serde_json::from_str(&format!(
            r#"{{"max_depth":10,"max_clause":4,"max_pred":1,"protect_h_preds":{value}}}"#
        ))
        .expect("failed to parse config")
    };
    assert!(with("true").protect_h_preds);
    assert!(!with("false").protect_h_preds);
}

#[test]
fn protect_h_preds_keeps_background_predicates_out_of_hypothesis_heads() {
    let solutions = ancestor_solutions(true);
    let captured = background_redefinitions(&solutions);
    assert!(
        captured.is_empty(),
        "an invented predicate was captured by a background symbol:\n{}",
        captured.join("\n")
    );
}

#[test]
fn protect_h_preds_still_admits_the_invented_predicate_solution() {
    // Protection must not be so strong that it prevents invention itself:
    // pred_1 generalising over dad and mum has to remain reachable.
    let solutions = ancestor_solutions(true);
    assert!(
        solutions
            .iter()
            .any(|solution| solution.hypothesis.lines().any(|clause| {
                clause.starts_with("pred_") && clause.contains(":-dad(")
            })),
        "expected a solution defining an invented predicate over dad"
    );
}

#[test]
fn disabling_protect_h_preds_allows_background_predicates_to_be_captured() {
    // The negative case, proving the flag is load-bearing rather than inert.
    // Without protection a goal on the constant `dad` may resolve against a
    // hypothesis clause headed by an invented variable, binding that variable
    // to `dad` and leaving a clause that redefines a background predicate.
    //
    // Both assertions share one unprotected search because it is by far the
    // slowest thing in this file: capture yields hundreds of solutions, nearly
    // all of them rediscoveries of hypotheses already reachable without
    // invention.
    let unprotected = ancestor_solutions(false);
    let captured = background_redefinitions(&unprotected);
    assert!(
        !captured.is_empty(),
        "expected background predicate capture once protection is disabled"
    );

    let protected = ancestor_solutions(true).len();
    assert!(
        protected < unprotected.len(),
        "expected protection to prune the search: {protected} vs {}",
        unprotected.len()
    );
}

#[test]
fn map() {
    let app = App::from_setup_json("examples/map/config.json")
        .expect("failed to load config");
    // Grounded Double
    let solutions: Vec<Solution> = app.query_session("map([1,2,3],[2,4,6],double).").unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
    // Bind Double
    let solutions: Vec<Solution> = app.query_session("map([1,2,3],[2,4,6],X).").unwrap().collect();
    assert!(solutions.iter().any(|solution|solution.bindings.iter().any(|binding| *binding.0 == *"X" && binding.1 == "double")));
}

#[test]
fn odd_even() {
    const H1: &[&str] = &[
        "even(Arg_0):-prev(Arg_0,Arg_1),pred_1(Arg_1).",
        "pred_1(Arg_0):-prev(Arg_0,Arg_1),even(Arg_1).",
        "pred_1(Arg_0):-prev(Arg_0,Arg_1),zero(Arg_1).",
    ];

    const H2: &[&str] = &[
        "even(Arg_0):-prev(Arg_0,Arg_1),pred_1(Arg_1).",
        "pred_1(Arg_0):-prev(Arg_0,Arg_1),even(Arg_1).",
        "even(Arg_0):-zero(Arg_0).",
    ];

    let app = App::from_setup_json("examples/odd_even/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

#[test]
fn learn_map_double() {
    const H1: &[&str] = &[
        "map_double([Arg_0|Arg_1],[Arg_2|Arg_3],double):-double(Arg_0,Arg_2),map_double(Arg_1,Arg_3,double).",
        "double(Arg_0,Arg_1):-add(Arg_0,Arg_0,Arg_1).",
        "map_double([],[],Arg_0)."
    ];
    let app = App::from_setup_json("examples/map/learn_config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1]);
}

#[test]
fn trains() {
    const H1: &[&str] = &[
        "e(Arg_0):-has_car(Arg_0,Arg_1),pred_1(Arg_1).",
        "pred_1(Arg_0):-closed(Arg_0),short(Arg_0).",
    ];
    const H2: &[&str] = &[
        "e(Arg_0):-pred_1(Arg_0,Arg_1),closed(Arg_1).",
        "pred_1(Arg_0,Arg_1):-has_car(Arg_0,Arg_1),short(Arg_1).",
    ];
    const H3: &[&str] = &[
        "e(Arg_0):-pred_1(Arg_0,Arg_1),short(Arg_1).",
        "pred_1(Arg_0,Arg_1):-has_car(Arg_0,Arg_1),closed(Arg_1).",
    ];
    let app = App::from_setup_json("examples/trains/config.json")
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
    let app = App::from_setup_json("examples/parity/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1]);
}

// ── Top Program Construction tests ──

#[test]
fn top_prog_robots() {
    let mut app = App::from_setup_json("examples/robots/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    app.run_top_prog();
}

/// Regression test for the molecules example.
///
/// This example uses a negative example (`phenolic(benzene)`), which drives
/// negation-as-failure (`not/1`) during top program construction. The inner
/// proof spawned by `not/1` runs on the *shared* heap and used to leave
/// forward bindings (old_var -> freshly_built_high_addr) behind; a later heap
/// truncation by the outer proof then dangled those refs and panicked in
/// `deref_addr`. This test ensures top program construction completes and
/// produces a hypothesis without panicking.
#[test]
fn top_prog_molecules_not() {
    let mut app = App::from_setup_json("examples/molecules/phenolic.json")
        .expect("failed to load molecules setup")
        .auto(true);
    let result = app.run_top_prog();
    assert!(
        result.contains("phenolic("),
        "expected a phenolic hypothesis, got:\n{result}"
    );
}

#[test]
fn top_prog_trains() {
    let mut app = App::from_setup_json("examples/trains/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    let result = app.run_top_prog();
    assert_eq!(result.lines().count(),2);
    //This creates a valid hypothesis, but due to race conditions 
    //in multi-threading predicate names and ordering of body literals is not deterministic
    // assert!(result.lines().find(|line| *line == "e(Arg_0):-has_car(Arg_0,Arg_1),pred_1(Arg_1).").is_some());
    // assert!(result.lines().find(|line| *line == "pred_1(Arg_0):-short(Arg_0),closed(Arg_0).").is_some());
}
