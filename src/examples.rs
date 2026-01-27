// Broad test on example files to prove working state of application

use std::{fs, sync::Arc};

use serde::{Deserialize, Serialize};

use crate::{
    heap::{
        heap::{Cell, Heap},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    parser::{
        build_tree::TokenStream,
        execute_tree::{build_clause, execute_tree},
        tokeniser::tokenise,
    },
    predicate_modules::{load_predicate_module, maths, MATHS},
    program::predicate_table::PredicateTable,
    resolution::proof::Proof,
    BodyClause, Config, Examples, SetUp,
};

/// Load a .pl file into the predicate table and heap
fn load_file(file_path: &str, predicate_table: &mut PredicateTable, heap: &mut Vec<Cell>) {
    let file = fs::read_to_string(file_path)
        .unwrap_or_else(|_| panic!("Failed to read file: {}", file_path));
    let syntax_tree = TokenStream::new(tokenise(file).unwrap())
        .parse_all()
        .unwrap();

    execute_tree(syntax_tree, heap, predicate_table);
}

/// Load a test setup from a config.json file
fn load_setup(config_path: &str) -> (Config, PredicateTable, Vec<Cell>, Option<Examples>) {
    let mut heap = Vec::new();
    let mut predicate_table = PredicateTable::new();

    // Initialize and load maths module
    load_predicate_module(&mut predicate_table, &MATHS);

    let setup: SetUp = serde_json::from_str(
        &fs::read_to_string(config_path)
            .unwrap_or_else(|_| panic!("Failed to read config: {}", config_path)),
    )
    .unwrap_or_else(|e| panic!("Failed to parse config: {}", e));

    let config = setup.config;

    for file_path in setup.files {
        load_file(&file_path, &mut predicate_table, &mut heap);
    }

    for BodyClause { symbol, arity } in setup.body_predicates {
        predicate_table
            .set_body((SymbolDB::set_const(symbol), arity), true)
            .unwrap();
    }

    (config, predicate_table, heap, setup.examples)
}

/// Build goals from a query string onto a query heap
fn build_goals(query_text: &str, query_heap: &mut QueryHeap) -> Vec<usize> {
    let query = format!(":-{query_text}");
    let literals = match TokenStream::new(tokenise(query).unwrap())
        .parse_clause()
        .unwrap()
    {
        Some(crate::parser::build_tree::TreeClause::Directive(literals)) => literals,
        _ => panic!("Query: '{query_text}' incorrectly formatted"),
    };

    let clause = build_clause(literals, None, query_heap, true);
    clause.iter().cloned().collect()
}

/// Run a query and return whether it succeeded and the number of solutions found
fn run_query(
    query_text: &str,
    predicate_table: Arc<PredicateTable>,
    heap: Arc<Vec<Cell>>,
    config: Config,
) -> (bool, usize) {
    let mut query_heap = QueryHeap::new(heap, None).unwrap();
    let goals = build_goals(query_text, &mut query_heap);

    let mut proof = Proof::new(query_heap, &goals, config);
    let mut solutions = 0;

    while proof.prove(predicate_table.clone(), config, config.debug) {
        solutions += 1;
        // Continue to find more solutions (backtrack)
    }

    // if proof.prove(predicate_table.clone(), config, config.debug) {
    //     solutions = 1;
    //     if proof.prove(predicate_table.clone(), config, config.debug) {
    //         solutions = 2;
    //     }
    // }

    (solutions > 0, solutions)
}

#[test]
fn ancestor() {
    let (config, predicate_table, heap, examples) = load_setup("examples/ancestor/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    // Run positive examples
    if let Some(Examples { pos, neg }) = examples {
        // Combine positive examples into a single query
        let mut query = String::new();
        for example in &pos {
            if !query.is_empty() {
                query += ",";
            }
            query += example;
        }
        query += ".";

        let (success, solutions) = run_query(&query, predicate_table.clone(), heap.clone(), config);

        println!(
            "Ancestor test: success={}, solutions={}",
            success, solutions
        );
        assert!(success, "Expected at least one solution for ancestor test");
    } else {
        panic!("No examples in ancestor config");
    }
}

#[test]
fn map() {
    // Initialize symbol database
    // SymbolDB::new();

    let (config, predicate_table, heap, examples) = load_setup("examples/map/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    // Run positive examples
    if let Some(Examples { pos, neg }) = examples {
        // Combine positive examples into a single query
        let mut query = String::new();
        for example in &pos {
            if !query.is_empty() {
                query += ",";
            }
            query += example;
        }
        query += ".";

        let (success, solutions) = run_query(&query, predicate_table.clone(), heap.clone(), config);

        println!("Map test: success={}, solutions={}", success, solutions);
        assert!(success, "Expected at least one solution for map test");
    } else {
        panic!("No examples in map config");
    }
}

#[test]
fn ancestor_learning() {
    // Test that ancestor can learn hypotheses
    // SymbolDB::new();

    let (config, predicate_table, heap, _) = load_setup("examples/ancestor/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    // Query that requires learning
    let query = "ancestor(ken,james).";

    let mut query_heap = QueryHeap::new(heap, None).unwrap();
    let goals = build_goals(query, &mut query_heap);

    let mut proof = Proof::new(query_heap, &goals, config);

    if proof.prove(predicate_table.clone(), config, config.debug) {
        println!("Ancestor learning test succeeded");
        if proof.hypothesis.len() > 0 {
            println!("Learned hypothesis:");
            println!("{}", proof.hypothesis.to_string(&proof.heap));
        }
        assert!(true);
    } else {
        panic!("Expected ancestor learning to find a solution");
    }
}
