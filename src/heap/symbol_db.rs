use std::sync::{atomic::AtomicBool, Arc, Mutex, RwLock};

const KNOWN_SYMBOLS: &[&str] = &["false", "true"];

static SYMBOLS: RwLock<SymbolDB> = RwLock::new(SymbolDB {
    const_symbols: Vec::new(),
    var_symbols: Vec::new(),
    var_symbol_map: Vec::new(),
    strings: Vec::new()
});

static RAN_NEW: Mutex<bool> = Mutex::new(false);

/**Stores all symbols from compiled terms
 * The heap will use this to create term strings whilst allowing
 * operations done with the heap to only handle usize values
 */
pub struct SymbolDB {
    const_symbols: Vec<Arc<str>>,
    var_symbols: Vec<Arc<str>>,
    var_symbol_map: Vec<((usize, usize),usize)>, //Key: (Variable Ref addr, heap_id), Value: index to var symbols vec
    strings: Vec<Arc<str>>
}

impl SymbolDB {
    pub fn new() {
        let mut ran_new = RAN_NEW.lock().unwrap();
        if !*ran_new{
            for symbol in KNOWN_SYMBOLS{
                Self::set_const(symbol.to_string());
            }
            *ran_new = true;
        }

    }

    pub fn set_const(symbol: String) -> usize {
        let mut symbols = SYMBOLS.write().unwrap();
        let symbol: Arc<str> = symbol.into();
        match symbols
            .const_symbols
            .iter()
            .position(|e| *e == symbol)
        {
            Some(i) => i + isize::MAX as usize,
            None => {
                symbols.const_symbols.push(symbol);
                symbols.const_symbols.len() - 1 + isize::MAX as usize
            }
        }
    }

    pub fn set_var(symbol: String, addr: usize, heap_id: usize) {
        let mut symbols = SYMBOLS.write().unwrap();
        let symbol: Arc<str> = symbol.into();
        match symbols.var_symbols.iter().position(|e| *e == symbol) {
            Some(i) => {
                symbols.var_symbol_map.push(((addr,heap_id), i));
            }
            None => {
                symbols.var_symbols.push(symbol);
                let i = symbols.var_symbols.len() - 1;
                symbols
                    .var_symbol_map
                    .push(((addr,heap_id), i));
            }
        }
    }

    pub fn get_const(id: usize) -> Arc<str> {
        SYMBOLS.read().unwrap().const_symbols[id - isize::MAX as usize].clone()
    }

    pub fn get_var(addr: usize, heap_id: usize) -> Option<Arc<str>> {
        let symbols = SYMBOLS.read().unwrap();
        if let Some(((_,_), i)) = symbols
            .var_symbol_map
            .iter()
            .find(|(key, _)| *key == (addr,heap_id))
        {
            Some(symbols.var_symbols[*i].clone())
        } else {
            None
        }
    }

    /** Given either a ref addr or a const id this function will return the related symbol */
    pub fn get_symbol(id: usize, heap_id: usize) -> String {
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

    pub fn get_string(index: usize) -> Arc<str>{
        //TODO make this much more effecient
        SYMBOLS.read().unwrap().strings.get(index).unwrap().clone()
    }

    pub fn set_string(value: String) -> usize{
        let mut write_gaurd = SYMBOLS.write().unwrap();
        write_gaurd.strings.push(value.into());
        write_gaurd.strings.len()-1
    }

}
