// Broad test on example files to prove working state of application

use std::{fs, sync::Arc};

use crate::{
    BodyClause, Config, Examples, SetUp, heap::{heap::Cell, query_heap::QueryHeap, symbol_db::SymbolDB}, parser::{
        build_tree::TokenStream,
        execute_tree::{build_clause, execute_tree},
        tokeniser::tokenise,
    }, predicate_modules::load_all_modules, program::predicate_table::PredicateTable, resolution::proof::Proof
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

    load_all_modules(&mut predicate_table);

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
    println!("{}",clause.to_string(query_heap));
    clause.iter().cloned().collect()
}

/// Run a query and return whether it succeeded and the number of solutions found
fn run_query(
    query_text: &str,
    predicate_table: Arc<PredicateTable>,
    heap: Arc<Vec<Cell>>,
    config: Config,
) -> (bool, usize) {
    let mut query_heap = QueryHeap::new(heap, None);
    let goals = build_goals(query_text, &mut query_heap);

    let mut proof = Proof::new(query_heap, &goals);
    let mut solutions = 0;

    while proof.prove(predicate_table.clone(), config) {
        solutions += 1;
        // Continue to find more solutions (backtrack)
    }

    (solutions > 0, solutions)
}

#[test]
fn ancestor() {
    let (config, predicate_table, heap, examples) = load_setup("examples/ancestor/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    // Run positive examples
    if let Some(examples) = examples {
        let (success, solutions) = run_query(
            &examples.to_query(),
            predicate_table.clone(),
            heap.clone(),
            config,
        );

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
    let (config, predicate_table, heap, examples) = load_setup("examples/map/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    // Run positive examples
    if let Some(examples) = examples {
        let (success, solutions) = run_query(
            &examples.to_query(),
            predicate_table.clone(),
            heap.clone(),
            config,
        );

        println!("Map test: success={}, solutions={}", success, solutions);
        assert!(success, "Expected at least one solution for map test");
    } else {
        panic!("No examples in map config");
    }
}

#[test]
fn odd_even() {
    let (config, predicate_table, heap, examples) = load_setup("examples/odd_even/config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    if let Some(examples) = examples {
        let (success, solutions) = run_query(
            &examples.to_query(),
            predicate_table.clone(),
            heap.clone(),
            config,
        );
        println!(
            "Odd Even test: success={}, solutions={}",
            success, solutions
        );
        assert!(success, "Expected at least one solution for map test");
    } else {
        panic!("No examples in map config");
    }
}

#[test]
fn learn_map_double() {
    let (config, predicate_table, heap, examples) = load_setup("examples/map/learn_config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    if let Some(examples) = examples {
        let (success, solutions) = run_query(
            &examples.to_query(),
            predicate_table.clone(),
            heap.clone(),
            config,
        );
        println!(
            "Learn Map Double test: success={}, solutions={}",
            success, solutions
        );
        assert!(success, "Expected at least one solution for Learn Map Double test");
    } else {
        panic!("No examples in Learn Map Double config");
    }
}

#[test]
fn trains(){
    let (config, predicate_table, heap, examples) = load_setup("examples/map/learn_config.json");

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    if let Some(examples) = examples {
        let (success, solutions) = run_query(
            &examples.to_query(),
            predicate_table.clone(),
            heap.clone(),
            config,
        );
        println!(
            "Trains test: success={}, solutions={}",
            success, solutions
        );
        assert!(success, "Expected at least one solution for Trains test");
    } else {
        panic!("No examples in Trains config");
    }
}