use std::sync::RwLock;

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

static CONFIG: RwLock<Config> = RwLock::new(Config {
    share_preds: SHARE_PREDS, // Can H use known predicates
    max_h_clause: MAX_H_SIZE, // Max clause size of H
    max_h_pred: MAX_INVENTED, // Max number of invented predicate symbols
    debug: DEBUG, //Print Debug statements during solving. TODO allow for step by step debugging
    max_depth: MAX_DEPTH, //Maximum depth of SLD resolution
    learn: LEARN, //Allow matching to meta clauses
});

impl Config {
    pub fn set_share_preds(share_preds: bool) {
        CONFIG.write().unwrap().share_preds = share_preds;
    }
    
    pub fn set_max_h_clause(a: usize) {
        CONFIG.write().unwrap().max_h_clause = a;
    }
    
    pub fn set_max_h_pred(a: usize) {
        CONFIG.write().unwrap().max_h_pred = a;
    }
    
    pub fn set_debug(debug: bool) {
        CONFIG.write().unwrap().debug = debug;
    }
    
    pub fn set_max_depth(a: usize) {
        CONFIG.write().unwrap().max_depth = a;
    }
    
    pub fn set_learn(a: bool) {
        CONFIG.write().unwrap().learn = a;
    }
    
    pub fn set_config(config: Config){
        *CONFIG.write().unwrap() = config;
    }

    pub fn get_share_preds() -> bool {
        CONFIG.read().unwrap().share_preds
    }
    
    pub fn get_max_h_clause() -> usize {
        CONFIG.read().unwrap().max_h_clause
    }
    
    pub fn get_max_h_pred() -> usize {
        CONFIG.read().unwrap().max_h_pred
    }
    
    pub fn get_debug() -> bool {
        CONFIG.read().unwrap().debug
    }
    
    pub fn get_max_depth() -> usize {
        CONFIG.read().unwrap().max_depth
    }
    
    pub fn get_learn() -> bool {
        CONFIG.read().unwrap().learn
    }
    
    pub fn get_config() -> Config{
        CONFIG.read().unwrap().clone()
    }
}



