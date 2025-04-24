use std::{cmp::{self, PartialOrd}, ops::{Deref, DerefMut, Range}};

#[derive(PartialEq, Eq, Ord)]
struct SymbolArity(usize,usize);
impl PartialOrd for SymbolArity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => self.1.partial_cmp(&other.1),
            ord => return ord,
        }
    }
}

//TODO create predicate function type
struct PredicateFN;
enum PredClFn {
    Function(PredicateFN),
    Clauses(Range<usize>),
}

pub struct Predicate {
    symbol_arity: SymbolArity,
    body: bool, 
    predicate: PredClFn
}

pub struct PredicateTable(Vec<Predicate>);

impl PredicateTable{
    pub fn find_predicate(&self, symbol_arity: &SymbolArity) -> Result<usize,usize>{
        let mut lb: usize = 0;
        let mut ub: usize = self.len()-1;
        let mut mid:usize;
        while ub > lb{
            mid = (lb + ub)/2;
            match symbol_arity.cmp(&self[mid].symbol_arity) {
                std::cmp::Ordering::Less => ub = mid-1,
                std::cmp::Ordering::Equal => return Ok(mid),
                std::cmp::Ordering::Greater => lb = mid+1,
            }
        }
        match symbol_arity.cmp(&self[lb].symbol_arity) {
            cmp::Ordering::Less => Err(lb),
            cmp::Ordering::Equal => Ok(lb),
            cmp::Ordering::Greater => Err(lb+1),
        }
    }

    pub fn update_insert_predicate(&mut self, symbol: usize, arity: usize, body: bool, predicate: PredClFn){
        let symbol_arity = SymbolArity(symbol, arity);
        match self.find_predicate(&symbol_arity) {
            Ok(i) => {self[i] = Predicate{symbol_arity,body,predicate}},
            Err(new_i) => self.push(Predicate { symbol_arity, body, predicate}),
        }
    }

    pub fn get_predicate(&self, symbol: usize, arity: usize) -> Option<&PredClFn>{
        match self.find_predicate(&SymbolArity(symbol, arity)) {
            Ok(i) => Some(&self[i].predicate),
            Err(_) => None,
        }
    }
}



impl Deref for PredicateTable {
    type Target = Vec<Predicate>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for PredicateTable  {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests{
    use super::{Predicate, PredicateTable, SymbolArity, PredClFn};

    #[test]
    fn find_predicate(){
        let pred_table = PredicateTable(vec![
            Predicate{ symbol_arity: SymbolArity(1, 2), body: true, predicate: PredClFn::Clauses(0..1) }
        ]);
    }


    #[test]
    fn insert(){

    }
}