mod pred_module;
mod program;
mod solver;
mod terms;

use std::{fs, io, process::ExitCode};
use terms::{
    heap::Heap,
    atoms::{Atom, AtomHandler},
    clause::{Clause, ClauseHandler}
};
use program::Program;
use pred_module::config_mod;
use solver::start_proof;


const MAX_H_SIZE: usize = 3; //Max number of clauses in H
const MAX_INVENTED: usize = 1; //Max invented predicate symbols
const SHARE_PREDS: bool = false; //Can program and H share pred symbols
const DEBUG: bool = true;
const CONSTRAINT: &str = "<c>";

pub struct Config {
    pub share_preds: bool,
    pub max_clause: usize,
    pub max_invented: usize,
    pub debug: bool,
}

impl Config {
    pub fn new() -> Config {
        Config {
            share_preds: SHARE_PREDS,
            max_clause: MAX_H_SIZE,
            max_invented: MAX_INVENTED,
            debug: DEBUG,
        }
    }
}

pub struct State {
    pub config: Config,
    pub prog: Program,
    pub constraints: Vec<Clause>,
    pub heap: Heap,
}

impl State {
    pub fn new() -> State {
        let mut state = State {
            config: Config::new(),
            prog: Program::new(),
            heap: Heap::new(),
            constraints: vec![],
        };
        config_mod(&mut state.heap, &mut state.prog);
        return state;
    }

    pub fn parse_file(&mut self, path: &str) {
        let file = fs::read_to_string(path.to_string() + ".pl").expect("Unable to read file");
        let mut speech: bool = false;
        let mut quote: bool = false;
        let mut buf = String::new();
        for char in file.chars() {
            if !speech && !quote && char == '.' {
                if buf.trim().find(":-") == Some(0) {
                    self.handle_directive(&buf.trim()[2..]);
                } else {
                    let clause = Clause::parse_clause(&buf, &mut self.heap);
                    if buf.contains(CONSTRAINT){
                        self.prog.add_constraint(clause);
                    }else{
                        self.prog.add_clause(clause, &self.heap);
                    }
                }
                buf.clear();
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
                buf.push(char);
            }
        }
    }

    pub fn main_loop(&mut self) {
        let mut buf = String::new();
        loop {
            // buf.clear();
            io::stdin()
                .read_line(&mut buf)
                .expect("Error reading from console");

            if buf.contains('.') {
                let mut it = buf.split('.').peekable();
                let new_buf: String;
                loop {
                    let directive = it.next().unwrap();
                    if it.peek().is_none() {
                        new_buf = directive.to_owned();
                        break;
                    }
                    self.handle_directive(directive);
                }
                buf = new_buf;
            }
        }
    }

    fn handle_directive(&mut self, directive: &str) {
        let directive = directive.trim();
        let file_regex = regex::Regex::new(r"\[(?<file_path>[\w]+)\]").unwrap();
        if let Some(caps) = file_regex.captures(directive) {
            self.parse_file(&caps["file_path"]);
            self.prog.write_prog(&self.heap);
        } else {
            let goals = self.parse_goals(directive);
            println!("Start Proof");
            start_proof(goals, &mut self.prog, &mut self.config, &mut self.heap);
        }
    }

    fn parse_goals(&mut self, input: &str) -> Vec<Atom> {
        let mut goals: Clause = vec![];
        let mut buf = String::new();

        let mut brackets = 0;
        let mut sqr_brackets = 0;
        for char in input.chars() {
            match char {
                ',' => {
                    if brackets == 0 && sqr_brackets == 0 {
                        goals.push(Atom::parse(&buf, &mut self.heap, None));
                        buf = String::new();
                        continue;
                    }
                }
                ')' => brackets -= 1,
                '(' => brackets += 1,
                ']' => sqr_brackets -= 1,
                '[' => sqr_brackets += 1,
                _ => (),
            }
            buf.push(char);
        }
        goals.push(Atom::parse(&buf, &mut self.heap, None));
        goals.eq_to_ref(&mut self.heap);
        return goals;
    }
}
/*
TO DO only add vars to heap if choice is chosen
Remove terms from heap when no longer needed
New Clause rules: constraints, head can't be existing predicate
*/
fn main() -> ExitCode {
    let mut state = State::new();
    state.main_loop();
    ExitCode::SUCCESS
}
