use std::sync::{Arc, RwLock};

const KNOWN_SYMBOLS: &[&str] = &["false", "true"];

static SYMBOLS: RwLock<SymbolDB> = RwLock::new(SymbolDB {
    const_symbols: Vec::new(),
    var_symbols: Vec::new(),
    var_symbol_map: Vec::new(),
});

/**Stores all symbols from compiled terms
 * The heap will use this to create term strings whilst allowing
 * operations done with the heap to only handle usize values
 */
pub struct SymbolDB {
    const_symbols: Vec<Arc<str>>,
    var_symbols: Vec<Arc<str>>,
    var_symbol_map: Vec<(usize, usize)>, //Key: Variable Ref addr, Value: index to var symbols vec
}

impl SymbolDB {
    pub fn new() {
        for symbol in KNOWN_SYMBOLS{
            Self::set_const(symbol);
        }
    }

    pub fn set_const(symbol: &str) -> usize {
        let mut symbols = SYMBOLS.write().unwrap();
        match symbols
            .const_symbols
            .iter()
            .position(|e| *e == symbol.into())
        {
            Some(i) => i + isize::MAX as usize,
            None => {
                symbols.const_symbols.push(symbol.into());
                symbols.const_symbols.len() - 1 + isize::MAX as usize
            }
        }
    }

    pub fn set_var(symbol: &str, addr: usize) {
        let mut symbols = SYMBOLS.write().unwrap();
        match symbols.var_symbols.iter().position(|e| *e == symbol.into()) {
            Some(i) => {
                symbols.var_symbol_map.push((addr, i));
            }
            None => {
                symbols.var_symbols.push(symbol.into());
                let i = symbols.var_symbols.len() - 1;
                symbols
                    .var_symbol_map
                    .push((addr, i));
            }
        }
    }

    pub fn get_const(id: usize) -> Arc<str> {
        SYMBOLS.read().unwrap().const_symbols[id - isize::MAX as usize].clone()
    }

    pub fn get_var(addr: usize) -> Option<Arc<str>> {
        let symbols = SYMBOLS.read().unwrap();
        if let Some((_, i)) = symbols
            .var_symbol_map
            .iter()
            .find(|(heap_ref, _)| heap_ref == &addr)
        {
            Some(symbols.var_symbols[*i].clone())
        } else {
            None
        }
    }

    /** Given either a ref addr or a const id this function will return the related symbol */
    pub fn get_symbol(id: usize) -> String {
        //If id >= usize:Max/2 then it is a constant id and not a heap ref addr
        let symbols = SYMBOLS.read().unwrap();
        if id >= (isize::MAX as usize) {
            match symbols.const_symbols.get(id - isize::MAX as usize) {
                Some(symbol) => symbol.to_string(),
                None => panic!("Unkown const id"),
            }
        } else {
            match Self::get_var(id) {
                Some(symbol) => symbol.to_string(),
                None => format!("_{id}"),
            }
        }
    }
}
