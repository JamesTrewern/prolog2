const MAX_H_SIZE: usize = 2; //Max number of clauses in H
const MAX_INVENTED: usize = 0; //Max invented predicate symbols
const SHARE_PREDS: bool = false; //Can program and H share pred symbols
const DEBUG: bool = false;
const MAX_DEPTH: usize = usize::MAX;
const LEARN: bool = true;

#[derive(Clone, Copy)]
pub struct Config {
    pub share_preds: bool,
    pub max_h_clause: usize,
    pub max_h_pred: usize,
    pub debug: bool,
    pub max_depth: usize,
    pub learn: bool,
}



impl Config {
    pub fn new() -> Config {
        Config {
            share_preds: SHARE_PREDS, // Can H use known predicates
            max_h_clause: MAX_H_SIZE, // Max clause size of H
            max_h_pred: MAX_INVENTED, // Max number of invented predicate symbols
            debug: DEBUG, //Print Debug statements during solving. TODO allow for step by step debugging
            max_depth: MAX_DEPTH, //Maximum depth of SLD resolution
            learn: LEARN //Allow matching to meta clauses 
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