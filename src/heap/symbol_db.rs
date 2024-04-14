use std::collections::HashMap;

pub(super) struct SymbolDB{
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
            Some(i) => i + isize::MAX as usize,
            None => {
                self.const_symbols.push(symbol.into());
                self.const_symbols.len() - 1 + isize::MAX as usize
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
                self.var_symbol_map
                    .insert(addr, self.var_symbols.len() - 1);
            }
        }
    }

    pub fn get_const(&self, id: usize) -> &str{
        &self.const_symbols[id-isize::MAX as usize]
    }

    pub fn get_var(&self, addr: usize) -> &str{
        &self.var_symbols[self.var_symbol_map[&addr]]
    }

    pub fn get_symbol(&self, id: usize) ->&str{
        if id >= (isize::MAX as usize){
            self.get_const(id)
        }else{
            self.get_var(id)
        }
    }
}
