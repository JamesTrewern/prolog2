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
pub fn is_var(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    // goal_arg already derefs, so a Ref cell at this point is always unbound.
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Ref).into()
}

pub fn non_var(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    // goal_arg already derefs, so a Ref cell at this point is always unbound.
    (heap[goal_arg(heap, goal, 0)].0 != Tag::Ref).into()
}

/// `is_const/1`: succeeds if the argument is a constant (atom).
pub fn is_const(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Con).into()
}

/// `is_const/1`: succeeds if the argument is a constant (atom).
pub fn valid_functor(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    let tag = heap[goal_arg(heap, goal, 0)].0;
    (tag == Tag::Con || tag == Tag::Ref).into()
}

/// `is_int/1`: succeeds if the argument is an integer.
pub fn is_int(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Int).into()
}

/// `is_float/1`: succeeds if the argument is a float.
pub fn is_float(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Flt).into()
}

/// `is_number/1`: succeeds if the argument is an integer or a float.
pub fn is_number(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    matches!(heap[goal_arg(heap, goal, 0)], (Tag::Int, _) | (Tag::Flt, _)).into()
}

/// `is_string/1`: succeeds if the argument is a string literal.
pub fn is_string(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[goal_arg(heap, goal, 0)].0 == Tag::Stri).into()
}

/// `is_compound/1`: succeeds if the argument is a compound term (functor + args).
pub fn is_atomic(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (![Tag::Str,Tag::Comp,Tag::Tup,Tag::Set,Tag::Lis].contains(&heap[resolve(heap, goal_arg(heap, goal, 0))].0)).into()
}

/// `is_compound/1`: succeeds if the argument is a compound term (functor + args).
pub fn is_compound(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Comp).into()
}

/// `is_tup/1`: succeeds if the argument is a tuple.
pub fn is_tup(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Tup).into()
}

/// `is_set/1`: succeeds if the argument is a set.
pub fn is_set(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    (heap[resolve(heap, goal_arg(heap, goal, 0))].0 == Tag::Set).into()
}

/// `is_list/1`: succeeds if the argument is a proper list (including `[]`).
pub fn is_list(
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
        ("==", 2, equal),
        ("=\\=", 2, not_equal),
        ("\\=", 2, not_unify),
        ("=..", 2, univ),
        // Type checks
        ("var", 1, is_var),
        ("nonvar", 1, non_var),
        ("const", 1, is_const),
        ("valid_functor", 1, valid_functor),
        ("int", 1, is_int),
        ("float", 1, is_float),
        ("number", 1, is_number),
        ("string", 1, is_string),
        ("compound", 1, is_compound),
        ("tup", 1, is_tup),
        ("set", 1, is_set),
        ("list", 1, is_list),
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
    fn type_var() {
        let tw = tw();
        tw.assert_true("var(X).");
        tw.assert_false("var(hello).");
        tw.assert_false("var(42).");
        tw.assert_false("var(3.14).");
        tw.assert_false("X = hello, var(X).");
    }

    #[test]
    fn type_const() {
        let tw = tw();
        tw.assert_true("const(hello).");
        tw.assert_true("const('42').");
        tw.assert_false("const(42).");
        tw.assert_false("const(X).");
        tw.assert_false("const(\"hello\").");
    }

    #[test]
    fn type_int() {
        let tw = tw();
        tw.assert_true("int(42).");
        tw.assert_true("int(0).");
        tw.assert_false("int(3.14).");
        tw.assert_false("int(hello).");
        tw.assert_false("int(X).");
    }

    #[test]
    fn type_float() {
        let tw = tw();
        tw.assert_true("float(3.14).");
        tw.assert_false("float(42).");
        tw.assert_false("float(hello).");
        tw.assert_false("float(X).");
    }

    #[test]
    fn type_number() {
        let tw = tw();
        tw.assert_true("number(42).");
        tw.assert_true("number(3.14).");
        tw.assert_false("number(hello).");
        tw.assert_false("number(X).");
        tw.assert_false("number(\"hi\").");
    }

    #[test]
    fn type_string() {
        let tw = tw();
        tw.assert_true("string(\"hello\").");
        tw.assert_false("string(hello).");
        tw.assert_false("string(42).");
        tw.assert_false("string(X).");
    }

    #[test]
    fn type_compound() {
        let tw = tw();
        tw.assert_true("compound(f(x)).");
        tw.assert_true("compound(f(x,y,z)).");
        tw.assert_false("compound(hello).");
        tw.assert_false("compound(42).");
        tw.assert_false("compound(X).");
    }

    #[test]
    fn type_list() {
        let tw = tw();
        tw.assert_true("list([]).");
        tw.assert_true("list([a,b,c]).");
        tw.assert_true("list([1,2,3]).");
        tw.assert_false("list(hello).");
        tw.assert_false("list(X).");
        tw.assert_false("list([a|_])."); // partial list fails
    }

    #[test]
    fn type_set() {
        let tw = tw();
        tw.assert_true("set({a,b,c}).");
        tw.assert_false("set([a,b]).");
        tw.assert_false("set(hello).");
    }

    // ── Prolog-defined: atomic/1 and list/1 ────────────────────────────

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
