// Broad test on example files to prove working state of application
use std::process::ExitCode;

use crate::app::{App, Solution};

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
    let solutions: Vec<Solution> = app
        .query_session_from_examples()
        .unwrap()
        .inspect(|solution| println!("{}", solution.hypothesis))
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

#[test]
fn map() {
    let app = App::from_setup_json("examples/map/config.json")
        .expect("failed to load config")
        .auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
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
    let app = App::from_setup_json("examples/fsm/parity.json")
        .expect("failed to load config")
        .auto(true);
    test_solutions(app, &[]);
}

// ── Top Program Construction tests ──

#[test]
fn top_prog_robots() {
    let app = App::from_setup_json("examples/robots/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    let result = app.run();
    assert_eq!(result, ExitCode::SUCCESS);
}

#[test]
fn top_prog_trains() {
    let app = App::from_setup_json("examples/robots/tpc_config.json")
        .expect("failed to load config")
        .auto(true);
    let result = app.run();
    assert_eq!(result, ExitCode::SUCCESS);
}
