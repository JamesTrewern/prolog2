pub mod maths;

use crate::{
    heap::{query_heap::QueryHeap, symbol_db::SymbolDB},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
};

pub enum PredReturn {
    True,
    False,
    Binding(Vec<(usize, usize)>),
}

impl PredReturn {
    pub fn bool(value: bool) -> PredReturn {
        if value {
            PredReturn::True
        } else {
            PredReturn::False
        }
    }
}

//Take Proof and pointer to function call term and return true(possibly with binding), or false
pub type PredicateFunction = fn(&mut QueryHeap, &mut Hypothesis, usize) -> PredReturn;

pub type PredicateModule = &'static [(&'static str, usize, PredicateFunction)];

pub fn load_predicate_module(
    predicate_table: &mut PredicateTable,
    predicate_module: &PredicateModule,
) {
    for (symbol, arity, pred_fn) in predicate_module.iter() {
        let _ = predicate_table.insert_predicate_function(
            (SymbolDB::set_const((*symbol).to_string()), *arity),
            *pred_fn,
        );
    }
}

/// Math predicates module
pub static MATHS: PredicateModule = &[
    ("is", 2, maths::is_pred),
];
