const KNOWN_SYMBOLS: &[&str] = &["false", "true"];

pub(super) static mut SYMBOLS: SymbolDB = SymbolDB {
    const_symbols: Vec::new(),
    var_symbols: Vec::new(),
    var_symbol_map: Vec::new(),
};

/**Stores all symbols from compiled terms
 * The heap will use this to create term strings whilst allowing
 * operations done with the heap to only handle usize values
 */
pub struct SymbolDB {
    const_symbols: Vec<Box<str>>,
    var_symbols: Vec<Box<str>>,
    var_symbol_map: Vec<(usize, usize)>, //Key: Variable Ref addr, Value: index to var symbols vec
}

impl SymbolDB {
    pub fn new() {
        unsafe {
            SYMBOLS.const_symbols = KNOWN_SYMBOLS
                .iter()
                .map(|symbol| (*symbol).into())
                .collect::<Vec<Box<str>>>()
        }
    }

    pub fn set_const(symbol: &str) -> usize {
        unsafe {
            match SYMBOLS
                .const_symbols
                .iter()
                .position(|e| *e == symbol.into())
            {
                Some(i) => i + isize::MAX as usize,
                None => {
                    SYMBOLS.const_symbols.push(symbol.into());
                    SYMBOLS.const_symbols.len() - 1 + isize::MAX as usize
                }
            }
        }
    }

    pub fn set_var(symbol: &str, addr: usize) {
        unsafe {
            match SYMBOLS.var_symbols.iter().position(|e| *e == symbol.into()) {
                Some(i) => {
                    SYMBOLS.var_symbol_map.push((addr, i));
                }
                None => {
                    SYMBOLS.var_symbols.push(symbol.into());
                    SYMBOLS
                        .var_symbol_map
                        .push((addr, SYMBOLS.var_symbols.len() - 1));
                }
            }
        }
    }

    pub fn get_const(id: usize) -> &'static str {
        unsafe { &SYMBOLS.const_symbols[id - isize::MAX as usize] }
    }

    pub fn get_var(addr: usize) -> Option<&'static str> {
        unsafe {
            if let Some((_, i)) = SYMBOLS
                .var_symbol_map
                .iter()
                .find(|(heap_ref, _)| heap_ref == &addr)
            {
                Some(&SYMBOLS.var_symbols[*i])
            } else {
                None
            }
        }
    }

    /** Given either a ref addr or a const id this function will return the related symbol */
    pub fn get_symbol(id: usize) -> String {
        //If id >= usize:Max/2 then it is a constant id and not a heap ref addr
        unsafe {
            if id >= (isize::MAX as usize) {
                match SYMBOLS.const_symbols.get(id - isize::MAX as usize) {
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
}
