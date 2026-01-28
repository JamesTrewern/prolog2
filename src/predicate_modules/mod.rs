pub mod maths;
pub mod meta_predicates;

use std::sync::Arc;

use crate::{
    heap::{query_heap::QueryHeap, symbol_db::SymbolDB},
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
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
// pub type PredicateFunction = fn(&mut QueryHeap, &mut Hypothesis, usize) -> PredReturn;

// Meta predicate functions need additional context to spawn new proofs
pub type PredicateFunction = fn(
    &mut QueryHeap,
    &mut Hypothesis,
    usize,
    Arc<PredicateTable>,
    Config,
) -> PredReturn;

pub type PredicateModule = &'static [(&'static str, usize, PredicateFunction)];
// pub type MetaPredicateModule = &'static [(&'static str, usize, MetaPredicateFunction)];

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
static MATHS: PredicateModule = &[
    ("is", 2, maths::is_pred),
];

static META_PREDICATES: PredicateModule = &[("not", 1, meta_predicates::not)];

/// Load all predicate modules into the predicate table.
/// Add any new predicate modules here to ensure they are loaded consistently
/// across main.rs and test examples.
pub fn load_all_modules(predicate_table: &mut PredicateTable) {
    load_predicate_module(predicate_table, &MATHS);
    load_predicate_module(predicate_table, &META_PREDICATES);
}
