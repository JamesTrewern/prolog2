use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicBool, Ordering::{Acquire,Relaxed}},
        Arc, Mutex, RwLock,
    },
};

const KNOWN_SYMBOLS: &[&str] = &["false", "true"];

static SYMBOLS: RwLock<SymbolDB> = RwLock::new(SymbolDB {
    const_symbols: Vec::new(),
    // var_symbols: Vec::new(),
    var_symbol_map: None,
    strings: Vec::new(),
});

static RUN_NEW: AtomicBool = AtomicBool::new(true);

/**Stores all symbols from compiled terms
 * The heap will use this to create term strings whilst allowing
 * operations done with the heap to only handle usize values
 */
pub struct SymbolDB {
    const_symbols: Vec<Arc<str>>,
    var_symbol_map: Option<HashMap<(usize, usize), Arc<str>>>, //Key: (Variable Ref addr, heap_id), Value: index to var symbols vec
    strings: Vec<Arc<str>>,
}

impl SymbolDB {
    pub fn get_vars_mut(&mut self) -> &mut HashMap<(usize, usize), Arc<str>> {
        match &mut self.var_symbol_map {
            Some(map) => map,
            None => panic!("Map should not be none"),
        }
    }

    pub fn get_vars(&self) -> &HashMap<(usize, usize), Arc<str>> {
        match &self.var_symbol_map {
            Some(map) => map,
            None => panic!("Map should not be none"),
        }
    }

    pub fn new() {
        if RUN_NEW.swap(false, Acquire) {
            let mut symbol_db = SYMBOLS.write().unwrap();
            for symbol in KNOWN_SYMBOLS {
                symbol_db.const_symbols.push(symbol.to_string().into());
            }
            symbol_db.var_symbol_map = Some(HashMap::new());
        }
    }

    pub fn set_const(symbol: String) -> usize {
        Self::new();
        let mut symbols = SYMBOLS.write().unwrap();
        let symbol: Arc<str> = symbol.into();
        match symbols.const_symbols.iter().position(|e| *e == symbol) {
            Some(i) => i + isize::MAX as usize,
            None => {
                symbols.const_symbols.push(symbol);
                symbols.const_symbols.len() - 1 + isize::MAX as usize
            }
        }
    }

    pub fn set_var(symbol: String, addr: usize, heap_id: usize) {
        Self::new();
        SYMBOLS
            .write()
            .unwrap()
            .get_vars_mut()
            .insert((addr, heap_id), symbol.into());
    }

    pub fn get_const(id: usize) -> Arc<str> {
        Self::new();
        SYMBOLS.read().unwrap().const_symbols[id - isize::MAX as usize].clone()
    }

    pub fn get_var(addr: usize, heap_id: usize) -> Option<Arc<str>> {
        Self::new();
        SYMBOLS
            .read()
            .unwrap()
            .get_vars()
            .get(&(addr, heap_id))
            .map(|symbol| symbol.clone())
    }

    /** Given either a ref addr or a const id this function will return the related symbol */
    pub fn get_symbol(id: usize, heap_id: usize) -> String {
        Self::new();
        //If id >= usize:Max/2 then it is a constant id and not a heap ref addr
        let symbols = SYMBOLS.read().unwrap();
        if id >= (isize::MAX as usize) {
            match symbols.const_symbols.get(id - isize::MAX as usize) {
                Some(symbol) => symbol.to_string(),
                None => panic!("Unkown const id"),
            }
        } else {
            match Self::get_var(id, heap_id) {
                Some(symbol) => symbol.to_string(),
                None => format!("_{id}"),
            }
        }
    }

    pub fn get_string(index: usize) -> Arc<str> {
        Self::new();
        //TODO make this much more effecient
        SYMBOLS.read().unwrap().strings.get(index).unwrap().clone()
    }

    pub fn set_string(value: String) -> usize {
        Self::new();
        let mut write_gaurd = SYMBOLS.write().unwrap();
        write_gaurd.strings.push(value.into());
        write_gaurd.strings.len() - 1
    }

    pub fn see_var_map() {
        Self::new();
        let symbols = SYMBOLS.read().unwrap();
        for (k,v) in symbols.get_vars(){
            println!("{k:?}:\t{v}")
        }
    }
}
