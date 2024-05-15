use std::{collections::HashMap, fs};

use crate::{clause::*, heap::Heap, pred_module::get_module, program::Program, solver::start_proof};

const MAX_H_SIZE: usize = 2; //Max number of clauses in H
const MAX_INVENTED: usize = 0; //Max invented predicate symbols
const SHARE_PREDS: bool = false; //Can program and H share pred symbols
const DEBUG: bool = true;
const HEAP_SIZE: usize = 2056;
const MAX_DEPTH: usize = 4;

static CONSTRAINT: &'static str = ":<c>-";
static IMPLICATION: &'static str = ":-";

#[derive(Clone, Copy)]
pub struct Config {
    pub share_preds: bool,
    pub max_clause: usize,
    pub max_invented: usize,
    pub debug: bool,
    pub max_depth: usize,
}

pub struct ConfigBuilder {
    config: Config,
}

pub struct State {
    pub prog: Program,
    pub config: Config,
    pub heap: Heap,
}

impl Config {
    pub fn new() -> Config {
        Config {
            share_preds: SHARE_PREDS,
            max_clause: MAX_H_SIZE,
            max_invented: MAX_INVENTED,
            debug: DEBUG,
            max_depth: MAX_DEPTH,
        }
    }

    pub fn max_h_size(&mut self, a: usize) -> Config {
        self.max_clause = a;
        *self
    }

    pub fn max_invented(&mut self, a: usize) -> Config {
        self.max_invented = a;
        *self
    }

    pub fn max_depth(&mut self, a: usize) -> Config {
        self.max_depth = a;
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
        State {
            config,
            prog,
            heap
        }
    }

    pub fn load_file(&mut self, path: &str) {
        self.heap.query_space = false;
        let mut file = fs::read_to_string(format!("{path}.pl")).expect("Unable to read file");
        remove_comments(&mut file);
        self.parse_prog(file);
    }

    pub fn parse_prog(&mut self, file: String){
        let mut speech: bool = false;
        let mut quote: bool = false;
        let mut i1 = 0;
        for (i2, char) in file.chars().enumerate() {
            if !speech && !quote && char == '.' {
                let segment = file[i1..i2].trim();
                if Some(0) == segment.find(":-") {
                    self.handle_directive(&segment[2..]);
                } else {
                    let (mut clause_type, clause) = Clause::parse_clause(segment, &mut self.heap);
                    let sym_arr = self.heap.str_symbol_arity(clause[0]);
                    if self.prog.body_preds.contains(&sym_arr){
                        clause_type = ClauseType::BODY;
                    }
                    self.prog.add_clause(clause_type, clause);
                }
                i1 = i2 + 1;
            } else {
                match char {
                    '"' => {
                        if !quote {
                            speech = !speech
                        }
                    }
                    '\'' => {
                        if !speech {
                            quote = !quote
                        }
                    }
                    _ => (),
                }
            }
        }
        self.heap.query_space = true;
        self.prog.clauses.sort_clauses();
        self.prog.clauses.find_flags();
        self.prog.predicates = self.prog.clauses.predicate_map(&self.heap);
    }

    pub fn parse_goals(&mut self, text: &str) -> Vec<usize>{
        let mut i1 = 0;
        let mut in_brackets = (0, 0);
        let mut goal_literals: Vec<&str> = vec![];
        for (i2, c) in text.chars().enumerate() {
            match c {
                '(' => {
                    in_brackets.0 += 1;
                }
                ')' => {
                    if in_brackets.0 == 0 {
                        break;
                    }
                    in_brackets.0 -= 1;
                }
                '[' => {
                    in_brackets.1 += 1;
                }
                ']' => {
                    if in_brackets.1 == 0 {
                        break;
                    }
                    in_brackets.1 -= 1;
                }
                ',' => {
                    if in_brackets == (0, 0) {
                        goal_literals.push(&text[i1..i2]);
                        i1 = i2 + 1
                    }
                }
                _ => (),
            }
            if i2 == text.len() - 1 {
                goal_literals.push(text[i1..].trim());
            }
        }
        let mut map: HashMap<String, usize> = HashMap::new();
        let goals: Vec<usize> = goal_literals
            .iter()
            .map(|text| self.heap.build_literal(text, &mut map, &vec![]))
            .collect();
        goals
    }

    pub fn handle_directive(&mut self, text: &str){
        let goals = self.parse_goals(text);
        start_proof(goals, self);
    }

    pub fn load_module(&mut self, name: &str){
        match  get_module(&name.to_lowercase()){
            Some(pred_module) => self.prog.add_pred_module(pred_module, &mut self.heap),
            None => println!("{name} is not a recognised module"),
        }
    }
}

fn remove_comments(file: &mut String) {
    //Must ingore % if in string
    let mut i = 0;
    let mut comment = false;
    loop {
        let c = match file.chars().nth(i) {
            Some(c) => c,
            None => break,
        };
        if c == '%' {
            let mut i2 = i;
            loop {
                i2 += 1;
                if file.chars().nth(i2) == Some('\n') || file.chars().nth(i2) == None {
                    file.replace_range(i..i2 + 1, "");
                    break;
                }
            }
        } else {
            i += 1;
        }
    }
}