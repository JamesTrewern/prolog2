use crate::{
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::unification::unify,
    Config,
};

use super::{PredReturn, PredicateModule};

/// Determine length of list
pub fn equal(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    heap._term_equal(goal + 2, goal + 3).into()
}

/// Determine length of list
pub fn not_equal(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    (!heap._term_equal(goal + 2, goal + 3)).into()
}

pub fn not_unify(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    unify(heap, goal + 2, goal + 3).is_none().into()
}

pub static DEFAULTS: PredicateModule = (
    &[("==", 2, equal), ("=\\=", 2, not_equal), ("\\=", 2, not_unify)],
    &[include_str!("../../builtins/defaults.pl")],
);

#[cfg(test)]
mod tests{
    use crate::app::App;
    use super::DEFAULTS;

    fn assert_binding(query: &str, expected_binding: (&str, &str), app: &App){
        let solution = app.query_session(query).unwrap().next().unwrap();
        let binding = &solution.bindings[0];
        assert_eq!(expected_binding.0,&*binding.0);
        assert_eq!(expected_binding.1,&*binding.1);
    }

    fn assert_false(query: &str, app: &App){
        assert!(app.query_session(query).unwrap().next().is_none())
    }

    fn assert_true(query: &str, app: &App){
        assert!(app.query_session(query).unwrap().next().is_some())
    }
    #[test]
    fn unify(){
        let app = App::new().load_module(&DEFAULTS).unwrap();
        assert_binding("X = X.", ("X","X"), &app);
        assert_binding("X = Y.", ("X","Y"), &app);
        assert_binding("X = 1.", ("X","1"), &app);
        assert_binding("1 = X.", ("X","1"), &app);
        assert_false("1 = 2.", &app);
    }

    #[test]
    fn not_unify(){
        let app = App::new().load_module(&DEFAULTS).unwrap();
        assert_false("X \\= X.", &app);
        assert_false("X \\= Y.", &app);
        assert_false("X \\= 1.", &app);
        assert_false("1 \\= X.", &app);
        assert_true("1 \\= 2.", &app);
    }

    #[test]
    fn not_equal(){
        let app = App::new().load_module(&DEFAULTS).unwrap();
        assert_false("X =\\= X.", &app);
        assert_true("X =\\= Y.", &app);
        assert_true("X =\\= 1.", &app);
        assert_true("1 =\\= 2.", &app);
    }

    #[test]
    fn equal(){
        let app = App::new().load_module(&DEFAULTS).unwrap();
        assert_true("X == X.", &app);
        assert_false("X == Y.", &app);
        assert_false("X == 1.", &app);
        assert_false("1 = 2.", &app);
    }
}