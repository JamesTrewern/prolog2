// #[cfg(test)]
// mod examples;
mod heap;
// mod interface;
mod parser;
mod predicate_modules;
mod program;
mod resolution;
use std::{
    collections::HashMap,
    fs,
    io::{stdin, stdout, Write},
    process::ExitCode,
    sync::Arc,
};

use console::Term;
use serde::{Deserialize, Serialize};

use crate::{
    heap::{
        heap::{Cell, Heap},
        query_heap::{self, QueryHeap},
        symbol_db::SymbolDB,
    },
    parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::{build_clause, execute_tree},
        tokeniser::tokenise,
    },
    program::{
        clause::Clause,
        predicate_table::{self, PredicateTable},
    },
    resolution::proof::{self, Proof},
};

#[derive(Clone, Copy, Serialize, Deserialize, Debug)]
struct Config {
    max_depth: usize,
    max_clause: usize,
    max_pred: usize,
}

#[derive(Serialize, Deserialize, Debug)]
struct BodyClause {
    symbol: String,
    arity: usize,
}

#[derive(Serialize, Deserialize, Debug)]
struct Examples {
    pos: Vec<String>,
    neg: Vec<String>,
}

#[derive(Serialize, Deserialize, Debug)]
struct SetUp {
    pub config: Config,
    pub body_predicates: Vec<BodyClause>,
    pub files: Vec<String>,
    pub examples: Option<Examples>
}

fn continue_proof() -> bool {
    let term = Term::stderr();
    loop {
        match term.read_key_raw().unwrap() {
            console::Key::Enter | console::Key::Backspace | console::Key::Char('.') => {
                return false
            }
            console::Key::Char(' ' | ';') | console::Key::Tab => return true,
            _ => (),
        }
    }
}

fn start_query(
    query_text: &str,
    predicate_table: Arc<PredicateTable>,
    heap: Arc<Vec<Cell>>,
    config: Config,
) -> Result<(), String> {
    let query = format!(":-{query_text}");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Query: '{query_text}' incorrectly formatted")),
    };

    let mut query_heap = QueryHeap::new(heap, None)?;
    let goals = build_clause(literals, None, &mut query_heap, true);
    let mut vars = Vec::new();
    for literal in goals.iter() {
        vars.extend(query_heap.term_vars(*literal, false).iter().map(|addr| {
            (
                SymbolDB::get_var(*addr, query_heap.get_id()).unwrap(),
                *addr,
            )
        }));
    }
    let mut proof = Proof::new(query_heap, &goals, config);

    loop {
        if proof.prove(predicate_table.clone(), config) {
            println!("TRUE");
            for (symbol, addr) in &vars {
                println!("{symbol} = {}", proof.heap.term_string(*addr))
            }
            //TODO display variable bindings
            if proof.hypothesis.len() != 0 {
                proof.hypothesis.print_hypothesis(&proof.heap);
            }
            if !continue_proof() {
                break;
            }
        } else {
            println!("FALSE");
            break;
        }
    }

    drop(proof);

    Ok(())
}

fn load_file(file_path: String, predicate_table: &mut PredicateTable, heap: &mut Vec<Cell>) {
    let file = fs::read_to_string(file_path).unwrap();
    let syntax_tree = TokenStream::new(tokenise(file).unwrap())
        .parse_all()
        .unwrap();

    execute_tree(syntax_tree, heap, predicate_table);
}

fn load_setup() -> (Config, PredicateTable, Vec<Cell>, Option<Examples>) {
    let mut heap = Vec::new();
    let mut predicate_table = PredicateTable::new();

    let setup: SetUp = serde_json::from_str(&fs::read_to_string("setup.json").unwrap()).unwrap();
    println!("{setup:?}");
    let config = setup.config;

    for file_path in setup.files {
        load_file(file_path, &mut predicate_table, &mut heap);
    }

    for BodyClause { symbol, arity } in setup.body_predicates {
        predicate_table
            .set_body((SymbolDB::set_const(symbol), arity), true)
            .unwrap();
    }

    (config, predicate_table, heap, setup.examples)
}

fn main() -> ExitCode {
    let (config, predicate_table, heap, examples) = load_setup();

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    let mut buffer = String::new();
    loop {
        if buffer.is_empty() {
            print!("?-");
            stdout().flush().unwrap();
        }
        match stdin().read_line(&mut buffer) {
            Ok(_) => {
                if buffer.contains('.') {
                    match start_query(&buffer, predicate_table.clone(), heap.clone(), config) {
                        Ok(_) => buffer.clear(),
                        Err(error) => println!("{error}"),
                    }
                } else {
                    continue;
                }
            }
            Err(error) => {
                println!("error: {error}");
                break;
            }
        }
    }
    ExitCode::SUCCESS
}
