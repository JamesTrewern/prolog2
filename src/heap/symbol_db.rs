use std::collections::HashMap;
use super::heap::Heap;

pub struct SymbolDB {
    const_symbols: Vec<Box<str>>,
    var_symbols: Vec<Box<str>>,
    var_symbol_map: HashMap<usize, usize>, //Key: Variable Ref addr, Value: index to var symbols vec
}

impl SymbolDB {
    pub fn new() -> SymbolDB {
        SymbolDB {
            const_symbols: vec![],
            var_symbols: vec![],
            var_symbol_map: HashMap::new(),
        }
    }
    pub fn set_const(&mut self, symbol: &str) -> usize {
        match self.const_symbols.iter().position(|e| *e == symbol.into()) {
            Some(i) => i + Heap::CON_PTR,
            None => {
                self.const_symbols.push(symbol.into());
                self.const_symbols.len() - 1 + Heap::CON_PTR
            }
        }
    }
    pub fn set_var(&mut self, symbol: &str, addr: usize) {
        match self.var_symbols.iter().position(|e| *e == symbol.into()) {
            Some(i) => {
                self.var_symbol_map.insert(addr, i);
            }
            None => {
                self.var_symbols.push(symbol.into());
                self.var_symbol_map.insert(addr, self.var_symbols.len() - 1);
            }
        }
    }

    pub fn get_const(&self, id: usize) -> &str {
        &self.const_symbols[id - Heap::CON_PTR]
    }

    pub fn get_var(&self, addr: usize) -> Option<&str> {
        if let Some(i) = self.var_symbol_map.get(&addr) {
            Some(&self.var_symbols[*i])
        } else {
            None
        }
    }

    pub fn get_symbol(&self, id: usize) -> String {
        if id >= (Heap::CON_PTR) {
            match self.const_symbols.get(id - Heap::CON_PTR) {
                Some(symbol) => symbol.to_string(),
                None => panic!("Unkown const id"),
            }
        } else {
            match self.get_var(id) {
                Some(symbol) => symbol.to_string(),
                None => format!("_{id}"),
            }
        }
    }
}
