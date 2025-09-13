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
    io::{stdin, stdout, Write},
    process::ExitCode,
};

use console::Term;

use crate::{
    heap::{
        heap::Heap,
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

#[derive(Clone, Copy)]
struct Config {
    max_depth: usize,
    max_clause: usize,
    max_pred: usize,
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
    predicate_table: &mut PredicateTable,
    config: Config,
) -> Result<(), String> {
    let query = format!(":-{query_text}");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Query: '{query_text}' incorrectly formatted")),
    };

    let mut heap = QueryHeap::new(None)?;
    let goals = build_clause(literals, None, &mut heap, true);
    let mut vars = Vec::new();
    for literal in goals.iter() {
        vars.extend(
            heap.term_vars(*literal, false)
                .iter()
                .map(|addr| (SymbolDB::get_var(*addr, heap.get_id()).unwrap(), *addr)),
        );
    }
    let mut proof = Proof::new(heap, &goals, predicate_table);

    loop {
        if proof.prove() {
            println!("TRUE");
            for (symbol, addr) in &vars{
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

fn main() -> ExitCode {
    let config = Config {
        max_depth: 100,
        max_clause: 0,
        max_pred: 0,
    };

    let mut predicate_table = PredicateTable::new();

    let mut buffer = String::new();
    loop {
        if buffer.is_empty() {
            print!("?-");
            stdout().flush().unwrap();
        }
        match stdin().read_line(&mut buffer) {
            Ok(_) => {
                if buffer.contains('.') {
                    match start_query(&buffer, &mut predicate_table, config) {
                        Ok(_) => continue,
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
