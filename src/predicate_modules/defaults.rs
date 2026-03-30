use crate::{
    heap::{
        heap::{Heap, Tag},
        query_heap::QueryHeap,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    resolution::unification::unify,
    Config,
};

use super::{helpers::*, PredReturn, PredicateModule};

// ---------------------------------------------------------------------------
// Unification / equality
// ---------------------------------------------------------------------------

/// `==/2`: structural equality without unification.
pub fn equal(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    heap.term_equal(goal + 2, goal + 3).into()
}

/// `=\=/2`: structural inequality without unification.
pub fn not_equal(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (!heap.term_equal(goal + 2, goal + 3)).into()
}

/// `\=/2`: succeeds if the two terms cannot be unified.
pub fn not_unify(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    unify(heap, goal + 2, goal + 3).is_none().into()
}

// ---------------------------------------------------------------------------
// =.. (univ)
// ---------------------------------------------------------------------------

/// `=../2`: convert between a compound term and a list of its functor + args.
pub fn univ(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    let compound = resolve(heap, goal_arg(heap, goal, 0));
    let list = goal_arg(heap, goal, 1);
    match (heap[compound].0, heap[list].0) {
        (Tag::Comp, Tag::Lis) => {
            // Build the equivalent list from compound args, then unify with
            // the existing list. Handles ground lists, partial lists with
            // variable tails, and variables in elements all in one shot.
            let comp_addrs: Vec<usize> = heap.str_iterator(compound).collect();
            let built_list = build_list_from_addrs(heap, &comp_addrs);
            match unify(heap, built_list, list) {
                Some(sub) => PredReturn::Success(sub.get_bindings().to_vec(), vec![]),
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

// ---------------------------------------------------------------------------
// Type checks
// ---------------------------------------------------------------------------

/// `is_var/1`: succeeds if the argument is an unbound variable.
pub fn is_var_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    // goal_arg already derefs, so a Ref cell at this point is always unbound.
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Ref).into()
}

/// `is_const/1`: succeeds if the argument is a constant (atom).
pub fn is_const_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Con).into()
}

/// `is_int/1`: succeeds if the argument is an integer.
pub fn is_int_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Int).into()
}

/// `is_float/1`: succeeds if the argument is a float.
pub fn is_float_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Flt).into()
}

/// `is_number/1`: succeeds if the argument is an integer or a float.
pub fn is_number_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    matches!(heap[goal_arg(heap, goal, 0)], (Tag::Int, _) | (Tag::Flt, _)).into()
}

/// `is_string/1`: succeeds if the argument is a string literal.
pub fn is_string_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Stri).into()
}

/// `is_compound/1`: succeeds if the argument is a compound term (functor + args).
pub fn is_compound_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Comp).into()
}

/// `is_tup/1`: succeeds if the argument is a tuple.
pub fn is_tup_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Tup).into()
}

/// `is_set/1`: succeeds if the argument is a set.
pub fn is_set_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Set).into()
}

/// `is_list/1`: succeeds if the argument is a proper list (including `[]`).
pub fn is_list_pred(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    let addr = goal_arg(heap, goal, 0);
    match heap[addr] {
        (Tag::ELis, _) => PredReturn::True,
        (Tag::Lis, _) => read_list_addrs(heap, addr).is_some().into(),
        _ => PredReturn::False,
    }
}

// ---------------------------------------------------------------------------
// Module registration
// ---------------------------------------------------------------------------

pub static DEFAULTS: PredicateModule = (
    &[
        // Unification / equality
        ("==",  2, equal),
        ("=\\=", 2, not_equal),
        ("\\=", 2, not_unify),
        ("=..", 2, univ),
        // Type checks
        ("is_var",      1, is_var_pred),
        ("is_const",    1, is_const_pred),
        ("is_int",      1, is_int_pred),
        ("is_float",    1, is_float_pred),
        ("is_number",   1, is_number_pred),
        ("is_string",   1, is_string_pred),
        ("is_compound", 1, is_compound_pred),
        ("is_tup",      1, is_tup_pred),
        ("is_set",      1, is_set_pred),
        ("is_list",     1, is_list_pred),
    ],
    &[include_str!("../../builtins/defaults.pl")],
);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::{super::helpers::TestWrapper, DEFAULTS};

    fn tw() -> TestWrapper {
        TestWrapper::new(&[DEFAULTS])
    }

    // ── unification / equality ────────────────────────────────────────────

    #[test]
    fn unify() {
        let tw = tw();
        tw.assert_binding("X = X.", ("X", "X"));
        tw.assert_binding("X = Y.", ("X", "Y"));
        tw.assert_binding("X = 1.", ("X", "1"));
        tw.assert_binding("1 = X.", ("X", "1"));
        tw.assert_false("1 = 2.");
    }

    #[test]
    fn not_unify() {
        let tw = tw();
        tw.assert_false("X \\= X.");
        tw.assert_false("X \\= Y.");
        tw.assert_false("X \\= 1.");
        tw.assert_false("1 \\= X.");
        tw.assert_true("1 \\= 2.");
    }

    #[test]
    fn not_equal() {
        let tw = tw();
        tw.assert_false("X =\\= X.");
        tw.assert_true("X =\\= Y.");
        tw.assert_true("X =\\= 1.");
        tw.assert_true("1 =\\= 2.");
    }

    #[test]
    fn equal() {
        let tw = tw();
        tw.assert_true("X == X.");
        tw.assert_false("X == Y.");
        tw.assert_false("X == 1.");
        tw.assert_false("1 = 2.");
    }

    // ── =.. (univ) ────────────────────────────────────────────────────────

    #[test]
    fn univ_var_list() {
        let tw = tw();
        tw.assert_binding("p(a,Y)=..X.", ("X", "[p,a,Y]"));
        tw.assert_binding("p(a,q(Y))=..X.", ("X", "[p,a,q(Y)]"));
    }

    #[test]
    fn univ_var_comp() {
        let tw = tw();
        tw.assert_binding("X=..[p,a,Y].", ("X", "p(a,Y)"));
        tw.assert_binding("X=..[p,a,q(Y)].", ("X", "p(a,q(Y))"));
    }

    #[test]
    fn univ_comp_list() {
        let tw = tw();
        tw.assert_false("p(a,b)=..[p,a].");
        tw.assert_false("p(a,b)=..[p,a,b,c].");
        tw.assert_true("p(a,b)=..[p,a,b].");
        tw.assert_bindings("p(a,b)=..[P,A,B].", &[("P", "p"), ("A", "a"), ("B", "b")]);
        tw.assert_bindings("p(A,B)=..[P,a,b].", &[("P", "p"), ("A", "a"), ("B", "b")]);
        tw.assert_bindings("p(a,b,c,d)=..[p,a|T].", &[("T", "[b,c,d]")]);
    }

    // ── type checks ───────────────────────────────────────────────────────

    #[test]
    fn type_is_var() {
        let tw = tw();
        tw.assert_true("is_var(X).");
        tw.assert_false("is_var(hello).");
        tw.assert_false("is_var(42).");
        tw.assert_false("is_var(3.14).");
        tw.assert_false("X = hello, is_var(X).");
    }

    #[test]
    fn type_is_const() {
        let tw = tw();
        tw.assert_true("is_const(hello).");
        tw.assert_true("is_const('42').");
        tw.assert_false("is_const(42).");
        tw.assert_false("is_const(X).");
        tw.assert_false("is_const(\"hello\").");
    }

    #[test]
    fn type_is_int() {
        let tw = tw();
        tw.assert_true("is_int(42).");
        tw.assert_true("is_int(0).");
        tw.assert_false("is_int(3.14).");
        tw.assert_false("is_int(hello).");
        tw.assert_false("is_int(X).");
    }

    #[test]
    fn type_is_float() {
        let tw = tw();
        tw.assert_true("is_float(3.14).");
        tw.assert_false("is_float(42).");
        tw.assert_false("is_float(hello).");
        tw.assert_false("is_float(X).");
    }

    #[test]
    fn type_is_number() {
        let tw = tw();
        tw.assert_true("is_number(42).");
        tw.assert_true("is_number(3.14).");
        tw.assert_false("is_number(hello).");
        tw.assert_false("is_number(X).");
        tw.assert_false("is_number(\"hi\").");
    }

    #[test]
    fn type_is_string() {
        let tw = tw();
        tw.assert_true("is_string(\"hello\").");
        tw.assert_false("is_string(hello).");
        tw.assert_false("is_string(42).");
        tw.assert_false("is_string(X).");
    }

    #[test]
    fn type_is_compound() {
        let tw = tw();
        tw.assert_true("is_compound(f(x)).");
        tw.assert_true("is_compound(f(x,y,z)).");
        tw.assert_false("is_compound(hello).");
        tw.assert_false("is_compound(42).");
        tw.assert_false("is_compound(X).");
    }

    #[test]
    fn type_is_list() {
        let tw = tw();
        tw.assert_true("is_list([]).");
        tw.assert_true("is_list([a,b,c]).");
        tw.assert_true("is_list([1,2,3]).");
        tw.assert_false("is_list(hello).");
        tw.assert_false("is_list(X).");
        tw.assert_false("is_list([a|_]).");  // partial list fails
    }

    #[test]
    fn type_is_set() {
        let tw = tw();
        tw.assert_true("is_set({a,b,c}).");
        tw.assert_false("is_set([a,b]).");
        tw.assert_false("is_set(hello).");
    }

    // ── Prolog-defined: atomic/1 and is_list/1 ────────────────────────────

    #[test]
    fn type_atomic() {
        let tw = tw();
        tw.assert_true("atomic(hello).");
        tw.assert_true("atomic(42).");
        tw.assert_true("atomic(3.14).");
        tw.assert_true("atomic(\"hi\").");
        tw.assert_false("atomic(X).");
        tw.assert_false("atomic(f(x)).");
    }
}
