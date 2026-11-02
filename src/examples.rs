// Broad test on example files to prove working state of application
use crate::app::{App, Solution};

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

    let app = App::from_setup_json("examples/ancestor/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

#[test]
fn map() {
    let app = App::from_setup_json("examples/map/config.json").expect("failed to load config");
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

    let app = App::from_setup_json("examples/odd_even/config.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[H1, H2]);
}

#[test]
fn learn_map_double() {
    const H1: &[&str] = &[
        "map_double([A|B],[C|D],double):-double(A,C),map_double(B,D,double).",
        "double(A,B):-add(A,A,B).",
        "map_double([],[],A)."
    ];
    let app = App::from_setup_json("examples/map/learn_config.json")
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
    app.run_parallel();
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
//     let mut app = App::from_setup_json("examples/molecules/phenolic.json")
//         .expect("failed to load molecules setup")
//         .auto(true);
//     let result = app.run_top_prog();
//     assert!(
//         result.contains("phenolic("),
//         "expected a phenolic hypothesis, got:\n{result}"
//     );
// }

#[test]
fn top_prog_trains() {
    let mut app = App::from_setup_json("examples/trains/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    let result = app.run_parallel().unwrap().pop().unwrap();
    assert_eq!(result.lines().count(), 2);
    //This creates a valid hypothesis, but due to race conditions
    //in multi-threading predicate names and ordering of body literals is not deterministic
    // assert!(result.lines().find(|line| *line == "e(A):-has_car(A,B),pred_1(B).").is_some());
    // assert!(result.lines().find(|line| *line == "pred_1(A):-short(A),closed(A).").is_some());
}

#[test]
fn colreg() {
    let mut app =
        App::from_setup_json("examples/colreg/setup_turn.json").expect("failed to load config");
    let _result = app.run_parallel();
}
