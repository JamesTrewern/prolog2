use manual_rwlock::MrwLock;
use console::Term;
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
    program::{dynamic_program::{DynamicProgram, Hypothesis}, program::Program},
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
                        self.handle_goal(&tokens).unwrap();
                        buffer.clear();
                    }
                }
                Err(error) => println!("error: {error}"),
            }
        }
    }

    pub fn handle_directive(&self, segment: &[&str]) -> Result<(), String> {
        // println!("Directive: {segment:?}");

        let goals = match parse_goals(segment) {
            Ok(res) => res,
            Err(error) => {
                println!();
                return Err(error);
            }
        };
        let mut store = Store::new(self.heap.read().unwrap());

        let mut seen_vars = HashMap::new();
        let goals: Box<[usize]> = goals
            .into_iter()
            .map(|t| t.build_to_heap(&mut store, &mut seen_vars, false))
            .collect();

        let mut proof = Proof::new(&goals, store, Hypothesis::None, None, self);
        proof.next();

        // self.heap.deallocate_above(*goals.first().unwrap());
        Ok(())
    }

    pub fn handle_goal(&self, segment: &[&str]) -> Result<(), String> {
        // println!("Directive: {segment:?}");

        let goals = match parse_goals(segment) {
            Ok(res) => res,
            Err(error) => {
                println!();
                return Err(error);
            }
        };
        let mut store = Store::new(self.heap.read().unwrap());

        let mut seen_vars = HashMap::new();
        let goals: Box<[usize]> = goals
            .into_iter()
            .map(|t| t.build_to_heap(&mut store, &mut seen_vars, false))
            .collect();

        let mut proof = Proof::new(&goals, store, Hypothesis::None, None, self);
        
        loop {
            if let Some(h) = proof.next(){
                if h.len() != 0{
                    println!("Hypothesis:");
                    for clause in h.iter(){
                        println!("\t{}",clause.to_string(&proof.store))
                    }
                }
                if !continue_proof(){
                    break;
                }
            }else{
                break;
            }
        }
        
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
                unsafe {
                    prog.early_release();
                    heap.early_release();
                }
                if let Err(msg) = self.handle_directive(segment) {
                    println!("Error after ln[{line}]: {msg}");
                    return;
                }
                unsafe {
                    prog.try_reobtain().unwrap();
                    heap.try_reobtain().unwrap();
                }

                prog.organise_clause_table(&*heap);
            } else {
                // println!("{segment:?}");
                let clause = match parse_clause(segment) {
                    Ok(res) => res.to_heap(&mut *heap),
                    Err(msg) => {
                        println!("Error after ln[{line}]: {msg}");
                        return;
                    }
                };
                // println!("{}", clause.to_string(&*heap));
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
            // println!("{file}");
            self.parse_prog(file);
            Ok(())
        } else {
            Err(format!("File not found at {path}"))
        }
    }
}

unsafe impl Send for State {}
unsafe impl Sync for State {}

fn continue_proof() -> bool{
    let term = Term::stderr();
    loop {
        match term.read_key_raw().unwrap() {
            console::Key::Enter |  console::Key::Backspace | console::Key::Char('.') => return false,
            console::Key::Char(' '|';') | console::Key::Tab => return true,
            _ => (),
        }
    }
}