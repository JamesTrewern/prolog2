use super::parser::{parse_literals, remove_comments, tokenise};
use crate::{heap::heap::Heap, pred_module::get_module, program::{clause::Clause, program::Program}, resolution::solver::Proof};
use std::{collections::HashMap, fs, io::{self, stdout, Write}};

const MAX_H_SIZE: usize = 2; //Max number of clauses in H
const MAX_INVENTED: usize = 0; //Max invented predicate symbols
const SHARE_PREDS: bool = false; //Can program and H share pred symbols
const DEBUG: bool = false;
const HEAP_SIZE: usize = 2056;
const MAX_DEPTH: usize = usize::MAX;

#[derive(Clone, Copy)]
pub struct Config {
    pub share_preds: bool,
    pub max_h_clause: usize,
    pub max_h_pred: usize,
    pub debug: bool,
    pub max_depth: usize,
}

pub struct State {
    pub prog: Program,
    pub config: Config,
    pub heap: Heap,
}

impl Config {
    pub fn new() -> Config {
        Config {
            share_preds: SHARE_PREDS, // Can H use known predicates
            max_h_clause: MAX_H_SIZE, // Max clause size of H
            max_h_pred: MAX_INVENTED, // Max number of invented predicate symbols
            debug: DEBUG, //Print Debug statements during solving. TODO allow for step by step debugging
            max_depth: MAX_DEPTH, //Maximum depth of SLD resolution
        }
    }

    pub fn max_h_clause(&mut self, a: usize) -> Config {
        self.max_h_clause = a;
        *self
    }

    pub fn max_h_preds(&mut self, a: usize) -> Config {
        self.max_h_pred = a;
        *self
    }

    pub fn max_depth(&mut self, a: usize) -> Config {
        self.max_depth = a;
        *self
    }

    pub fn debug(&mut self, debug: bool) -> Config {
        self.debug = debug;
        *self
    }

    pub fn share_preds(&mut self, share_preds: bool) -> Config {
        self.share_preds = share_preds;
        *self
    }
}

impl State {
    pub fn new(config: Option<Config>) -> State {
        let config = if let Some(config) = config {
            config
        } else {
            Config::new()
        };
        let mut prog = Program::new();
        let mut heap = Heap::new(HEAP_SIZE);
        prog.add_pred_module(crate::pred_module::CONFIG, &mut heap);
        prog.add_pred_module(crate::pred_module::MATH, &mut heap);

        State { config, prog, heap }
    }

    pub fn load_file(&mut self, path: &str) -> Result<(),String>{
        self.heap.query_space = false;
        if let Ok(mut file) = fs::read_to_string(format!("{path}.pl")){
            remove_comments(&mut file);
            self.parse_prog(file);
            self.heap.query_space = true;
            self.heap.query_space_pointer = self.heap.len();
            Ok(())
        }else{
            Err(format!("File not found at {path}"))
        }
        
    }

    pub fn parse_prog(&mut self, file: String) {
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
                if let Err(msg) = self.handle_directive(segment) {
                    println!("Error after ln[{line}]: {msg}");
                    return;
                }
            } else {
                let terms = match parse_literals(segment) {
                    Ok(res) => res,
                    Err(msg) => {
                        println!("Error after ln[{line}]: {msg}");
                        return;
                    }
                };
                self.prog.add_clause(Clause::parse_clause(terms, &mut self.heap), &self.heap);
            }

            line += segment.iter().filter(|t| **t == "\n").count();
        }
        self.heap.query_space = true;
        self.prog.organise_clause_table(&self.heap);
    }

    pub fn handle_directive(&mut self, segment: &[&str]) -> Result<(), String> {
        let goals = match parse_literals(segment) {
            Ok(res) => res,
            Err(error) => {
                println!();
                return Err(error);
            }
        };

        let mut var_ref = HashMap::new();
        let goals: Box<[usize]> = goals
            .into_iter()
            .map(|t| t.build_on_heap(&mut self.heap, &mut var_ref))
            .collect();
        let mut proof = Proof::new(&goals, self);
        proof.next();
        self.heap.deallocate_above(*goals.first().unwrap());
        Ok(())
    }

    pub fn load_module(&mut self, name: &str) {
        match get_module(&name.to_lowercase()) {
            Some(pred_module) => self.prog.add_pred_module(pred_module, &mut self.heap),
            None => println!("{name} is not a recognised module"),
        }
    }

    pub fn main_loop(&mut self){
        let mut buffer = String::new();
        loop{
            if buffer.is_empty(){
                print!("?-");
                stdout().flush().unwrap();
            }
            match io::stdin().read_line(&mut buffer) {
                Ok(_) => {
                    let tokens = tokenise(&buffer);
                    if tokens.contains(&"."){
                        self.handle_directive(&tokens).unwrap();
                        buffer.clear();
                    }
                }
                Err(error) => println!("error: {error}"),
            }
        }
    }
}
