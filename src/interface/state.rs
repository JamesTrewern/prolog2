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
    program::program::{DynamicProgram, Program},
    resolution::solver::Proof, //resolution::solver::Proof,
};

use std::{
    cell::UnsafeCell,
    collections::HashMap,
    fs,
    io::{self, stdout, Write},
};

pub struct State {
    pub config: UnsafeCell<Config>,
    pub program: MrwLock<Program>,
    pub heap: MrwLock<Vec<Cell>>,
}

impl State {
    pub fn new(config: Option<Config>) -> State {
        SymbolDB::new();
        let config = if let Some(config) = config {
            UnsafeCell::new(config)
        } else {
            UnsafeCell::new(Config::new())
        };
        let program = MrwLock::new(Program::new());
        let heap = MrwLock::new(Vec::new());

        let mut state = State {
            config,
            program,
            heap,
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
                self.program
                    .try_write()
                    .unwrap()
                    .add_pred_module(pred_module.0);
            }
            None => println!("{name} is not a recognised module"),
        }
    }

    pub fn main_loop(&mut self) {
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

    pub fn handle_directive(&mut self, segment: &[&str]) -> Result<(), String> {
        println!("directive: {segment:?}");

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
            .map(|t| t.build_to_heap(&mut store, &mut seen_vars, false))
            .collect();
        let mut proof = Proof::new(
            &goals,
            store,
            DynamicProgram::new(None, self.program.read().unwrap()),
            None,
            self,
        );
        proof.next();

        // self.heap.deallocate_above(*goals.first().unwrap());
        Ok(())
    }

    pub fn parse_prog(&mut self, file: String) {
        let mut store = Store::new(self.heap.read_slice().unwrap());
        let mut prog = self.program.try_write().unwrap();
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
                drop(prog);
                self.to_static_heap(&mut store);
                if let Err(msg) = self.handle_directive(segment) {
                    println!("Error after ln[{line}]: {msg}");
                    return;
                }
                prog = self.program.write().unwrap();
            } else {
                let clause = match parse_clause(segment) {
                    Ok(res) => res.to_heap(&mut store),
                    Err(msg) => {
                        println!("Error after ln[{line}]: {msg}");
                        return;
                    }
                };
                prog.add_clause(clause, &mut store);
            }

            line += segment.iter().filter(|t| **t == "\n").count();
        }
        // self.heap.query_space = true;
        prog.organise_clause_table(&mut store);
        drop(prog);
        self.to_static_heap(&mut store);
    }

    pub fn load_file(&mut self, path: &str) -> Result<(), String> {
        if let Ok(mut file) = fs::read_to_string(format!("{path}.pl")) {
            remove_comments(&mut file);
            self.parse_prog(file);
            Ok(())
        } else {
            Err(format!("File not found at {path}"))
        }
    }

    pub fn to_static_heap(&mut self, store: &mut Store) {
        unsafe { store.prog_cells.early_release() };
        let mut prog_heap = self.heap.try_write().unwrap();
        unsafe {
            // TO DO drop reference to heap, ask for write lock on heap
            assert!(
                prog_heap.len() == store.prog_cells.len(),
                "Another thread has mutated program heap",
            );
            prog_heap.append(&mut store.cells);
            store.prog_cells = self.heap.read_slice().unwrap();
        };
    }
}
