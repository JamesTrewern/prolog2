//! Every config shipped in the repository still deserialises.
//!
//! `Config` is `deny_unknown_fields`, so a config carrying a field name the
//! engine no longer knows is a hard error rather than a silently ignored key.
//! That is the behaviour we want -- a stale `"top_prog": true` would otherwise
//! deserialise to no `parallel` block and quietly run a direct query instead
//! of learning -- but it also means the shipped configs and the `Config` struct
//! have to be kept in step. This is the test that notices when they are not.
//!
//! Deliberately parses only the config, without loading the `.pl` files or
//! running anything: the question is whether the config *shape* is valid, and
//! answering it should stay fast enough to run on every build.

use std::{
    fs,
    path::{Path, PathBuf},
};

use prolog2::Config;

/// Every `.json` under `examples/`, plus the default `config.json`.
fn shipped_configs() -> Vec<PathBuf> {
    fn walk(dir: &Path, found: &mut Vec<PathBuf>) {
        let entries = fs::read_dir(dir).unwrap_or_else(|e| panic!("reading {dir:?}: {e}"));
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, found);
            } else if path.extension().is_some_and(|e| e == "json") {
                found.push(path);
            }
        }
    }

    let mut found = vec![PathBuf::from("config.json")];
    walk(Path::new("examples"), &mut found);
    found.sort();
    found
}

#[test]
fn every_shipped_config_deserialises() {
    let configs = shipped_configs();
    assert!(
        configs.len() > 1,
        "found no example configs -- the test is looking in the wrong place"
    );

    let mut failures = Vec::new();
    for path in &configs {
        let text = match fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) => {
                failures.push(format!("{}: could not read: {e}", path.display()));
                continue;
            }
        };
        if let Err(e) = serde_json::from_str::<Config>(&text) {
            failures.push(format!("{}: {e}", path.display()));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} shipped configs failed to parse:\n  {}",
        failures.len(),
        configs.len(),
        failures.join("\n  ")
    );
}

/// The learning configs select learning by carrying a `parallel` block, and
/// the query configs select a direct query by omitting it.
///
/// Pinned because the two are now distinguished by presence rather than by a
/// boolean: if `parallel` ever stopped deserialising, every one of these would
/// silently become a query config, which looks like a learning failure rather
/// than a config error.
#[test]
fn learning_configs_carry_a_parallel_block() {
    let learns = [
        "examples/colreg/avoid.json",
        "examples/colreg/resume.json",
        "examples/colreg/take_action.json",
        "examples/colreg/turn.json",
        "examples/molecules/hydroxyl.json",
        "examples/robots/tpc_config.json",
        "examples/trains/tpc_config.json",
        "config.json",
    ];
    let queries = [
        "examples/ancestor/config.json",
        "examples/molecules/phenolic.json",
        "examples/mtg/config.json",
        "examples/robots/config.json",
        "examples/trains/config.json",
    ];

    for path in learns {
        let config: Config = serde_json::from_str(&fs::read_to_string(path).unwrap())
            .unwrap_or_else(|e| panic!("{path}: {e}"));
        assert!(
            config.parallel.is_some(),
            "{path} is a learning config and must carry a parallel block"
        );
    }
    for path in queries {
        let config: Config = serde_json::from_str(&fs::read_to_string(path).unwrap())
            .unwrap_or_else(|e| panic!("{path}: {e}"));
        assert!(
            config.parallel.is_none(),
            "{path} runs a direct query and must not carry a parallel block"
        );
    }
}

/// An omitted `final_h_count` takes its default rather than zero, which would
/// silently return no programs at all.
#[test]
fn final_h_count_defaults_rather_than_zeroing() {
    let config: Config = serde_json::from_str(
        r#"{"resolution":{"max_depth":5,"max_clause":2},"body_predicates":[],
            "files":[],"examples":null,"parallel":{"reduce":true}}"#,
    )
    .expect("minimal config should parse");
    let parallel = config.parallel.expect("parallel block was given");
    assert_eq!(
        parallel.final_h_count,
        prolog2::ParallelConfig::default().final_h_count
    );
    assert_ne!(parallel.final_h_count, 0);
    assert!(parallel.reduce);
    assert!(!parallel.sort_by_literals);
}

/// A field name from an older version is an error, not an ignored key.
#[test]
fn a_stale_field_name_is_rejected() {
    let err = serde_json::from_str::<Config>(
        r#"{"resolution":{"max_depth":5,"max_clause":2},"body_predicates":[],
            "files":[],"examples":null,"top_prog":true,"reduce":true}"#,
    )
    .expect_err("top_prog was replaced by parallel and must not be silently ignored");
    assert!(
        err.to_string().contains("top_prog"),
        "the error should name the offending field, got: {err}"
    );
}
