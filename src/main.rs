#[cfg(test)]
mod examples;
mod heap;
// mod interface;
mod parser;
mod predicate_modules;
mod program;
mod resolution;
mod top_prog;
use std::{
    env, fs,
    io::{stdin, stdout, Write},
    process::ExitCode,
    sync::Arc,
};

use console::Term;
use serde::{Deserialize, Serialize};

use crate::{
    heap::{
        heap::{Cell, Heap},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::{build_clause, execute_tree},
        tokeniser::tokenise,
    },
    predicate_modules::load_all_modules,
    program::predicate_table::PredicateTable,
    resolution::proof::Proof,
};

#[derive(Clone, Copy, Serialize, Deserialize, Debug)]
struct Config {
    max_depth: usize,
    max_clause: usize,
    max_pred: usize,
    #[serde(default)]
    debug: bool,
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
    pub examples: Option<Examples>,
    #[serde(default)]
    pub top_prog: bool,
}

impl Examples {
    pub fn to_query(&self) -> String{
        let mut buffer = String::new();
        for pos_ex in &self.pos{
            buffer += pos_ex;
            buffer += ",";
        }
        for neg_ex in &self.neg{
            buffer += &format!("not({neg_ex}),");
        }
        buffer.pop();
        buffer += ".";
        buffer
    }
}

fn continue_proof(auto: bool) -> bool {
    if auto {
        return true;
    }
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
    auto: bool,
) -> Result<(), String> {
    let query = format!(":-{query_text}");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Query: '{query_text}' incorrectly formatted")),
    };

    let mut query_heap = QueryHeap::new(heap, None);
    let goals = build_clause(literals, None, None, &mut query_heap, true);
    let mut vars = Vec::new();
    for literal in goals.iter() {
        vars.extend(query_heap.term_vars(*literal, false).iter().map(|addr| {
            (
                SymbolDB::get_var(*addr, query_heap.get_id()).unwrap(),
                *addr,
            )
        }));
    }
    let mut proof = Proof::new(query_heap, &goals);

    loop {
        if proof.prove(predicate_table.clone(), config) {
            println!("TRUE");
            for (symbol, addr) in &vars {
                println!("{symbol} = {}", proof.heap.term_string(*addr))
            }
            //TODO display variable bindings
            if proof.hypothesis.len() != 0 {
                println!("{}", proof.hypothesis.to_string(&proof.heap));
            }
            if !continue_proof(auto) {
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

fn load_setup(config_path: &str) -> (Config, PredicateTable, Vec<Cell>, Option<Examples>, bool) {
    let mut heap = Vec::new();
    let mut predicate_table = PredicateTable::new();

    load_all_modules(&mut predicate_table);

    let setup: SetUp = serde_json::from_str(
        &fs::read_to_string(config_path)
            .unwrap_or_else(|_| panic!("Failed to read config file: {}", config_path)),
    )
    .unwrap_or_else(|e| panic!("Failed to parse config file '{}': {}", config_path, e));
    let config = setup.config;

    for file_path in setup.files {
        load_file(file_path, &mut predicate_table, &mut heap);
    }

    for BodyClause { symbol, arity } in setup.body_predicates {
        let sym = SymbolDB::set_const(symbol.clone());
        predicate_table
            .set_body((sym, arity), true)
            .unwrap_or_else(|e| panic!("{e}: {symbol}/{arity}"));
    }

    (config, predicate_table, heap, setup.examples, setup.top_prog)
}

fn main_loop(
    config: Config,
    predicate_table: Arc<PredicateTable>,
    heap: Arc<Vec<Cell>>,
) -> ExitCode {
    let mut buffer = String::new();
    loop {
        if buffer.is_empty() {
            print!("?-");
            stdout().flush().unwrap();
        }
        match stdin().read_line(&mut buffer) {
            Ok(_) => {
                if buffer.contains('.') {
                    match start_query(
                        &buffer,
                        predicate_table.clone(),
                        heap.clone(),
                        config,
                        false,
                    ) {
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

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    let auto = args.iter().any(|arg| arg == "--all" || arg == "-a");

    let config_path = args
        .iter()
        .filter(|arg| !arg.starts_with('-') && *arg != &args[0])
        .next()
        .map(|s| s.as_str())
        .unwrap_or("setup.json");

    let (config, predicate_table, heap, examples, top_prog_mode) = load_setup(config_path);

    let predicate_table = Arc::new(predicate_table);
    let heap = Arc::new(heap);

    if top_prog_mode {
        match examples {
            Some(examples) => top_prog::run(examples, predicate_table, heap, config),
            None => {
                eprintln!("top_prog mode requires examples in config");
                ExitCode::FAILURE
            }
        }
    } else {
        match examples {
            Some(examples) => {
                start_query(&examples.to_query(), predicate_table, heap, config, auto).unwrap();
                ExitCode::SUCCESS
            }
            None => main_loop(config, predicate_table, heap),
        }
    }
}
