// Broad test on example files to prove working state of application
use std::process::ExitCode;

use crate::{app::{App, Solution}};
        
#[test]
fn ancestor() {
    let app = App::from_setup_json("examples/ancestor/config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

#[test]
fn map() {
    let app = App::from_setup_json("examples/map/config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

#[test]
fn odd_even() {   
    let app = App::from_setup_json("examples/odd_even/config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

#[test]
fn learn_map_double() {
    let app = App::from_setup_json("examples/map/learn_config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

#[test]
fn trains() {
    let app = App::from_setup_json("examples/trains/config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

#[test]
fn fsm_parity() {
    let app = App::from_setup_json("examples/fsm/config.json").auto(true);
    let solutions: Vec<Solution> = app.query_session_from_examples().unwrap().collect();
    assert!(solutions.len() > 0, "Expected at least one solution");
}

// ── Top Program Construction tests ──

#[test]
fn top_prog_robots() {
    let app = App::from_setup_json("examples/robots/tpc_config.json").auto(true);
    let result = app.run();
    assert_eq!(result, ExitCode::SUCCESS);
}

#[test]
fn top_prog_trains() {
    let app = App::from_setup_json("examples/robots/tpc_config.json").auto(true);
    let result = app.run();
    assert_eq!(result, ExitCode::SUCCESS);
}
