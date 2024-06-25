use super::{
    config::Config,
    parser::{parse_clause, parse_goals, remove_comments, tokenise},
};
use crate::{
    heap::{store::Store, symbol_db::SymbolDB},
    pred_module::get_module,
    program::program::{DynamicProgram, PROGRAM},
    resolution::solver::Proof, //resolution::solver::Proof,
};
use std::{
    collections::HashMap,
    fs,
    io::{self, stdout, Write},
};

pub fn start(config: Option<Config>) {
    SymbolDB::new();
    if let Some(config) = config {
        Config::set_config(config);
    }
    load_module("config");
    load_module("maths");
    // load_module("meta_preds");
}

pub fn load_file(path: &str) -> Result<(), String> {
    if let Ok(mut file) = fs::read_to_string(format!("{path}.pl")) {
        remove_comments(&mut file);
        let mut store = Store::new();
        parse_prog(file, &mut store);
        store.to_prog();
        Ok(())
    } else {
        Err(format!("File not found at {path}"))
    }
}

pub fn parse_prog(file: String, store: &mut Store) {
    let mut line = 0;
    let tokens = tokenise(&file);
    'outer: for mut segment in tokens.split(|t| *t == ".") {
        loop {
            match segment.first() {
                Some(t) => {
                    if *t == "\n" {
                        line += 1;
                        segment = &segment[1..]
                    } else {
                        break;
                    }
                }
                None => continue 'outer,
            }
        }

        if segment[0] == ":-" {
            store.to_prog();
            if let Err(msg) = handle_directive(segment) {
                println!("Error after ln[{line}]: {msg}");
                return;
            }
        } else {
            let clause = match parse_clause(segment) {
                Ok(res) => res.to_heap(store),
                Err(msg) => {
                    println!("Error after ln[{line}]: {msg}");
                    return;
                }
            };
            PROGRAM.write().unwrap().add_clause(clause, store);
        }

        line += segment.iter().filter(|t| **t == "\n").count();
    }
    // self.heap.query_space = true;
    PROGRAM.write().unwrap().organise_clause_table(store);
}

pub fn handle_directive(segment: &[&str]) -> Result<(), String> {
    let goals = match parse_goals(segment) {
        Ok(res) => res,
        Err(error) => {
            println!();
            return Err(error);
        }
    };

    let mut store = Store::new();
    let mut seen_vars = HashMap::new();
    let goals: Box<[usize]> = goals
        .into_iter()
        .map(|t| t.build_to_heap(&mut store, &mut seen_vars, false))
        .collect();
    let mut proof = Proof::new(&goals, store, DynamicProgram::new(None), None);
    proof.next();

    // self.heap.deallocate_above(*goals.first().unwrap());
    Ok(())
}

pub fn load_module(name: &str) {
    match get_module(&name.to_lowercase()) {
        Some(pred_module) => {
            pred_module.1();
            PROGRAM.write().unwrap().add_pred_module(pred_module.0)
        }
        None => println!("{name} is not a recognised module"),
    }
}

pub fn main_loop() {
    let mut buffer = String::new();
    loop {
        if buffer.is_empty() {
            print!("?-");
            stdout().flush().unwrap();
        }
        match io::stdin().read_line(&mut buffer) {
            Ok(_) => {
                let tokens = tokenise(&buffer);
                if tokens.contains(&".") {
                    handle_directive(&tokens).unwrap();
                    buffer.clear();
                }
            }
            Err(error) => println!("error: {error}"),
        }
    }
}
