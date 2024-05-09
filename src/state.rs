use crate::{heap::Heap, program::Program};

const MAX_H_SIZE: usize = 2; //Max number of clauses in H
const MAX_INVENTED: usize = 0; //Max invented predicate symbols
const SHARE_PREDS: bool = false; //Can program and H share pred symbols
const DEBUG: bool = true;
const HEAP_SIZE: usize = 2056;
const MAX_DEPTH: usize = 4;
pub struct Config {
    pub share_preds: bool,
    pub max_clause: usize,
    pub max_invented: usize,
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
            share_preds: SHARE_PREDS,
            max_clause: MAX_H_SIZE,
            max_invented: MAX_INVENTED,
            debug: DEBUG,
            max_depth: MAX_DEPTH,
        }
    }
}

impl State {
    pub fn new(config: Option<Config>) -> State {
        let config = if let Some(config) = config {
            config
        } else{
            Config::new()
        };
        State {
            config,
            prog: Program::new(),
            heap: Heap::new(HEAP_SIZE),
        }
    }
}