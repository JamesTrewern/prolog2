use manual_rwlock::MrwLock;

use super::{
    config::Config,
    parser::{parse_clause, parse_goals, remove_comments, tokenise},
};
use crate::{
    heap::{
        store::{Cell, Store},
        symbol_db::SymbolDB,
    },
    pred_module::get_module,
    program::program::{DynamicProgram, ProgH, Program},
    resolution::solver::Proof, //resolution::solver::Proof,
};

use std::{
    collections::HashMap,
    fs,
    io::{self, stdout, Write},
    sync::{Arc, RwLock},
};

#[derive(Clone)]
pub struct State {
    pub config: Arc<RwLock<Config>>,
    pub program: Arc<MrwLock<Program>>,
    pub heap: Arc<MrwLock<Vec<Cell>>>,
}

impl State {
    pub fn new(config: Option<Config>) -> State {
        SymbolDB::new();
        let config = if let Some(config) = config {
            RwLock::new(config)
        } else {
            RwLock::new(Config::new())
        };
        let program = MrwLock::new(Program::new());
        let heap = MrwLock::new(Vec::new());

        let state = State {
            config: config.into(),
            program: program.into(),
            heap: heap.into(),
        };

        state.load_module("config");
        state.load_module("maths");
        state.load_module("meta_preds");

        state
    }

    pub fn load_module(&self, name: &str) {
        match get_module(&name.to_lowercase()) {
            Some(pred_module) => {
                pred_module.1();
                self.program.write().unwrap().add_pred_module(pred_module.0);
            }
            None => println!("{name} is not a recognised module"),
        }
    }

    pub fn main_loop(&self) {
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
                        self.handle_directive(&tokens).unwrap();
                        buffer.clear();
                    }
                }
                Err(error) => println!("error: {error}"),
            }
        }
    }

    pub fn handle_directive(&self, segment: &[&str]) -> Result<(), String> {
        let goals = match parse_goals(segment) {
            Ok(res) => res,
            Err(error) => {
                println!();
                return Err(error);
            }
        };
        let mut store = Store::new(self.heap.read_slice().unwrap());
        let mut seen_vars = HashMap::new();
        let goals: Box<[usize]> = goals
            .into_iter()
            .map(|t| {
                t.build_to_heap(&mut store.cells, &mut seen_vars, false) + store.prog_cells.len()
            })
            .collect();
        let mut proof = Proof::new(
            &goals,
            store,
            ProgH::None,
            None,
            self,
        );
        proof.next();

        // self.heap.deallocate_above(*goals.first().unwrap());
        Ok(())
    }

    pub fn parse_prog(&self, file: String) {
        let mut prog = self.program.try_write().unwrap();
        let mut heap = self.heap.try_write().unwrap();
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
                prog.organise_clause_table(&*heap);
                drop(prog);
                drop(heap);
                if let Err(msg) = self.handle_directive(segment) {
                    println!("Error after ln[{line}]: {msg}");
                    return;
                }
                prog = self.program.try_write().unwrap();
                heap = self.heap.try_write().unwrap();

                prog.organise_clause_table(&*heap);
            } else {
                let clause = match parse_clause(segment) {
                    Ok(res) => res.to_heap(&mut *heap),
                    Err(msg) => {
                        println!("Error after ln[{line}]: {msg}");
                        return;
                    }
                };
                prog.add_clause(clause, &*heap);
            }

            line += segment.iter().filter(|t| **t == "\n").count();
        }
        // self.heap.query_space = true;
        prog.organise_clause_table(&*heap);
        drop(prog);
    }

    pub fn load_file(&self, path: &str) -> Result<(), String> {
        if let Ok(mut file) = fs::read_to_string(format!("{path}.pl")) {
            remove_comments(&mut file);
            self.parse_prog(file);
            Ok(())
        } else {
            Err(format!("File not found at {path}"))
        }
    }
}

unsafe impl Send for State {}
unsafe impl Sync for State {}