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

use super::{PredReturn, PredicateModule, helpers::*};

/// Determine length of list
pub fn equal(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    heap.term_equal(goal + 2, goal + 3).into()
}

/// Determine length of list
pub fn not_equal(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    (!heap.term_equal(goal + 2, goal + 3)).into()
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

pub fn univ(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let compound = resolve(heap, goal_arg(heap, goal, 0));
    let list = goal_arg(heap, goal, 1);
    match (heap[compound].0, heap[list].0) {
        (Tag::Comp, Tag::Lis) => {
            // Build the equivalent list from compound args, then unify with existing list.
            // Handles ground lists, partial lists with variable tails, and variables in
            // elements — unify takes care of all of it.
            let comp_addrs: Vec<usize> = heap.str_iterator(compound).collect();
            let built_list = build_list_from_addrs(heap, &comp_addrs);
            println!("built_list: {}", heap.term_string(built_list));
            println!("list: {}", heap.term_string(list));
            match unify(heap, built_list, list) {
                Some(sub) => {PredReturn::Success(sub.get_bindings().to_vec(), vec![])},
                None => false.into(),
            }
        }
        (Tag::Comp, Tag::Ref) => {
            let comp_addrs: Vec<usize> = heap.str_iterator(compound).collect();
            let built_list = build_list_from_addrs(heap, &comp_addrs);
            PredReturn::Success(vec![(list, built_list)], vec![])
        }
        (Tag::Ref, Tag::Lis) => {
            let Some(addrs) = read_list_addrs(heap, list) else {
                return false.into();
            };
            let new_compound = build_compound_from_addrs(heap, &addrs);
            PredReturn::Success(vec![(compound, new_compound)], vec![])
        }
        _ => false.into(),
    }
}

pub fn is_var(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_const(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_compound(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_tup(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_set(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_int(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_float(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub fn is_string(
    heap: &mut QueryHeap,
    hypothesis: &mut Hypothesis,
    goal: usize,
    predicate_table: &PredicateTable,
    config: Config,
) -> PredReturn {
    todo!()
}

pub static DEFAULTS: PredicateModule = (
    &[
        ("==", 2, equal),
        ("=\\=", 2, not_equal),
        ("\\=", 2, not_unify),
        ("=..", 2, univ),
    ],
    &[include_str!("../../builtins/defaults.pl")],
);

#[cfg(test)]
mod tests {
    use super::{DEFAULTS,super::helpers::TestWrapper};

    fn test_wrapper() -> TestWrapper{
        TestWrapper::new(&[DEFAULTS])
    }

    fn assert_binding(query: &str, expected: (&str, &str)) {
        test_wrapper().assert_binding(query, expected);
    }

    fn assert_bindings(query: &str, expected: &[(&str, &str)]) {
        test_wrapper().assert_bindings(query, expected);
    }

    fn assert_false(query: &str) {
        test_wrapper().assert_false(query);
    }

    fn assert_true(query: &str) {
        test_wrapper().assert_true(query);
    }
    #[test]
    fn unify() {
        assert_binding("X = X.", ("X", "X"), );
        assert_binding("X = Y.", ("X", "Y"), );
        assert_binding("X = 1.", ("X", "1"), );
        assert_binding("1 = X.", ("X", "1"), );
        assert_false("1 = 2.", );
    }

    #[test]
    fn not_unify() {
        assert_false("X \\= X.", );
        assert_false("X \\= Y.", );
        assert_false("X \\= 1.", );
        assert_false("1 \\= X.", );
        assert_true("1 \\= 2.", );
    }

    #[test]
    fn not_equal() {
        assert_false("X =\\= X.", );
        assert_true("X =\\= Y.", );
        assert_true("X =\\= 1.", );
        assert_true("1 =\\= 2.", );
    }

    #[test]
    fn equal() {
        assert_true("X == X.", );
        assert_false("X == Y.", );
        assert_false("X == 1.", );
        assert_false("1 = 2.", );
    }

    #[test]
    fn univ_var_list(){
        assert_binding("p(a,Y)=..X.", ("X","[p,a,Y]"));
        assert_binding("p(a,q(Y))=..X.", ("X","[p,a,q(Y)]"));
    }

    #[test]
    fn univ_var_comp(){
        assert_binding("X=..[p,a,Y].", ("X","p(a,Y)"));
        assert_binding("X=..[p,a,q(Y)].", ("X","p(a,q(Y))"));
    }
    
    #[test]
    fn univ_comp_list(){
        assert_false("p(a,b)=..[p,a].");
        assert_false("p(a,b)=..[p,a,b,c].");
        assert_true("p(a,b)=..[p,a,b].");
        assert_bindings("P(A,B)=..[p,a,b].", &[("P","p"),("A","a"),("B","b")]);
        assert_bindings("p(a,b)=..[P,A,B].", &[("P","p"),("A","a"),("B","b")]);

    }

}
