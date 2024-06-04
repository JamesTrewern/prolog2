use super::{config::Config, parser::{parse_clause, parse_goals, remove_comments, tokenise}};
use crate::{heap::heap::Heap, pred_module::get_module, program::program::Program, resolution::solver::Proof};
use std::{collections::HashMap, fs, io::{self, stdout, Write}};

const HEAP_SIZE: usize = 2056;

pub struct State {
    pub prog: Program,
    pub config: Config,
    pub heap: Heap,
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
        prog.add_pred_module(crate::pred_module::MATHS, &mut heap);

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
                let clause = match parse_clause(segment) {
                    Ok(res) => res.to_heap(&mut self.heap),
                    Err(msg) => {
                        println!("Error after ln[{line}]: {msg}");
                        return;
                    }
                };
                self.prog.add_clause(clause, &self.heap);
            }

            line += segment.iter().filter(|t| **t == "\n").count();
        }
        self.heap.query_space = true;
        self.prog.organise_clause_table(&self.heap);
    }

    pub fn handle_directive(&mut self, segment: &[&str]) -> Result<(), String> {
        let goals = match parse_goals(segment) {
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
            Some(pred_module) => {pred_module.1(self); self.prog.add_pred_module(pred_module.0, &mut self.heap)},
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
