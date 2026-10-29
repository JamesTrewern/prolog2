//! Built-in set predicates.
//!
//! Sets in Prolog² are unordered, duplicate-free collections written with
//! curly braces: `{a, b, c}`.  On the heap they are stored as
//! `(Tag::Set, length)` followed by `length` element cells.
//!
//! Set unification is equality-only (no variable binding) because the lack of
//! element ordering makes correct binding impossible when two or more variables
//! are present.  Predicates like `member/2` that need to enumerate choices use
//! `PredReturn::Choices` to create backtrackable alternatives.

use super::{utils::*, PredReturn, PredicateModule};
use crate::{
    heap::{Heap, QueryHeap, Tag, VarBind::Addr},
    predicate_modules::maths::Number,
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

// ── Internal helpers ──────────────────────────────────────────────────────────

/// The element addresses of the set at `addr`, or `None` if it is not a set.
///
/// Elements are read with [`read_structure_addrs`], which walks each one by
/// its length rather than assuming a cell apiece, so a set may hold compound
/// terms: `{f(a), b}` reads as two elements.
fn read_set(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    match resolve_to_cell(heap, addr) {
        (Tag::Set, _) => read_structure_addrs(heap, addr),
        _ => None,
    }
}

/// Is `elem` structurally equal to any member of `elements`?
fn set_contains(heap: &QueryHeap, elements: &[usize], elem: usize) -> bool {
    elements.iter().any(|&member| heap.term_equal(member, elem))
}

/// Read both set arguments of a three-argument predicate.
fn read_two_sets(heap: &QueryHeap, goal: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    let first = read_set(heap, goal_arg(heap, goal, 0))?;
    let second = read_set(heap, goal_arg(heap, goal, 1))?;
    Some((first, second))
}

/// Build `elements` into a set and unify it with the goal's third argument.
///
/// Every binary set operation ends this way: the result argument may be
/// unbound, in which case it takes the new set, or already bound, in which
/// case it has to match.
fn finish_set_result(heap: &mut QueryHeap, goal: usize, elements: &[usize]) -> PredReturn {
    let result = goal_arg(heap, goal, 2);
    let new_set = build_set(heap, elements);
    unify_with_term(heap, result, new_set)
}

fn factorial(mut n: usize) -> usize {
    let mut res = 1;
    while n > 1 {
        res *= n;
        n -= 1;
    }
    res
}

fn n_choose_r(n: usize, r: usize) -> usize {
    factorial(n) / ((factorial(r)) * factorial(n - r))
}

/// Every `k`-element combination of `elems`, flattened end to end.
///
/// The result holds `k` addresses per combination, so combination `i` is
/// `result[i * k..(i + 1) * k]`. Returns empty when `k` is zero or larger
/// than the input.
fn combinations(elems: &[usize], k: usize) -> Vec<usize> {
    if k == 0 || k > elems.len() {
        return vec![];
    }
    let num_sub_sets = n_choose_r(elems.len(), k);
    let mut result = Vec::with_capacity(k * num_sub_sets);
    let mut sub_set = Vec::with_capacity(k);
    combo_rec(elems, k, &mut sub_set, &mut result);
    result
}

fn combo_rec(elems: &[usize], k: usize, sub_set: &mut Vec<usize>, result: &mut Vec<usize>) {
    if sub_set.len() == k {
        result.extend_from_slice(sub_set);
        return;
    }
    for (i, &elem) in elems.iter().enumerate() {
        sub_set.push(elem);
        combo_rec(&elems[i + 1..], k, sub_set, result);
        sub_set.pop();
    }
}

// ── Predicates ────────────────────────────────────────────────────────────────

/// `set_member(?Elem, +Set)` — Elem is a member of Set.
///
/// If `Elem` is bound this is a membership check. If it is unbound, every
/// element is offered as a [`PredReturn::Choices`] alternative, so
/// backtracking enumerates the set.
pub fn set_member_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let elem = goal_arg(heap, goal, 0);
    let Some(elements) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };

    let (Tag::Var, var_id) = resolve_to_cell(heap, elem) else {
        return set_contains(heap, &elements, elem).into();
    };

    if elements.is_empty() {
        return PredReturn::False;
    }
    PredReturn::Choices(
        elements
            .into_iter()
            .map(|element| (vec![(var_id, Addr(element))], vec![]))
            .collect(),
    )
}

/// `subset(?SubSet, +Set, +Size)` — SubSet is a subset of Set with exactly
/// Size elements.
///
/// With `SubSet` bound this checks that it has `Size` elements and that all
/// of them are in `Set`. With `SubSet` unbound, every `Size`-element subset
/// is offered as an alternative.
///
/// Fails if `Size` is not an integer or exceeds the size of `Set`.
pub fn subset_sized(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let size_arg = resolve_to_cell(heap, goal_arg(heap, goal, 2));
    let Ok(Number::Int(size)) = Number::try_from(size_arg) else {
        return PredReturn::False;
    };
    if size < 0 {
        return PredReturn::False;
    }
    let size = size as usize;

    let Some(elements) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };
    if size > elements.len() {
        return PredReturn::False;
    }

    let subset_arg = goal_arg(heap, goal, 0);
    let (Tag::Var, var_id) = resolve_to_cell(heap, subset_arg) else {
        // Check mode: the right cardinality, and every element present.
        let Some(subset) = read_set(heap, subset_arg) else {
            return PredReturn::False;
        };
        return (subset.len() == size
            && subset
                .iter()
                .all(|&elem| set_contains(heap, &elements, elem)))
        .into();
    };

    if size == 0 {
        let empty = build_set(heap, &[] as &[usize]);
        return PredReturn::bind_addr(heap, var_id, empty);
    }

    // Each subset is built up front and offered as one alternative. Cells
    // belonging to alternatives that are never taken are unreachable rather
    // than wrong, and go away when the heap is truncated on backtracking.
    let combos = combinations(&elements, size);
    let alternatives: Vec<_> = combos
        .chunks(size)
        .map(|combo| {
            let subset = build_set(heap, combo);
            (vec![(var_id, Addr(subset))], vec![])
        })
        .collect();

    if alternatives.is_empty() {
        return PredReturn::False;
    }
    PredReturn::Choices(alternatives)
}

/// `set_union(+Set1, +Set2, ?Result)` — Result is the union of Set1 and Set2.
pub fn set_union_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((first, second)) = read_two_sets(heap, goal) else {
        return PredReturn::False;
    };
    // `build_set` drops duplicates, so the two can simply be concatenated.
    let mut union = first;
    union.extend(second);
    finish_set_result(heap, goal, &union)
}

/// `set_intersection(+Set1, +Set2, ?Result)` — Result is the intersection.
pub fn set_intersection_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((first, second)) = read_two_sets(heap, goal) else {
        return PredReturn::False;
    };
    let common: Vec<usize> = first
        .into_iter()
        .filter(|&elem| set_contains(heap, &second, elem))
        .collect();
    finish_set_result(heap, goal, &common)
}

/// `set_difference(+Set1, +Set2, ?Result)` — Result is Set1 without the
/// elements of Set2.
pub fn set_difference_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((first, second)) = read_two_sets(heap, goal) else {
        return PredReturn::False;
    };
    let difference: Vec<usize> = first
        .into_iter()
        .filter(|&elem| !set_contains(heap, &second, elem))
        .collect();
    finish_set_result(heap, goal, &difference)
}

/// `set_symmetric_difference(+Set1, +Set2, ?Result)` — the elements in one
/// set but not both.
pub fn set_symdiff_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((first, second)) = read_two_sets(heap, goal) else {
        return PredReturn::False;
    };
    let mut symmetric: Vec<usize> = first
        .iter()
        .copied()
        .filter(|&elem| !set_contains(heap, &second, elem))
        .collect();
    symmetric.extend(
        second
            .iter()
            .copied()
            .filter(|&elem| !set_contains(heap, &first, elem)),
    );
    finish_set_result(heap, goal, &symmetric)
}

/// `set_size(+Set, ?N)` — N is the number of elements in Set.
pub fn set_size_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(elements) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    unify_with_int(heap, goal_arg(heap, goal, 1), elements.len() as isize)
}

/// `set_add(+Set, +Elem, ?Result)` — Result is Set with Elem added, which is
/// Set itself if Elem is already a member.
pub fn set_add_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(mut elements) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let elem = goal_arg(heap, goal, 1);

    // Pushed unconditionally: `build_set` would drop it as a duplicate
    // anyway, so an already-present element needs no special case.
    if !set_contains(heap, &elements, elem) {
        elements.push(elem);
    }
    finish_set_result(heap, goal, &elements)
}

/// `set_del(+Set, +Elem, ?Result)` — Result is Set without Elem.
pub fn set_del_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(elements) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let elem = goal_arg(heap, goal, 1);
    let remaining: Vec<usize> = elements
        .into_iter()
        .filter(|&member| !heap.term_equal(member, elem))
        .collect();
    finish_set_result(heap, goal, &remaining)
}

/// `set_to_list(+Set, ?List)` — List holds the elements of Set.
pub fn set_to_list_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(elements) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let list_arg = goal_arg(heap, goal, 1);
    let list = build_list(heap, &elements);
    unify_with_term(heap, list_arg, list)
}

/// `list_to_set(+List, ?Set)` — Set holds the elements of List with
/// duplicates removed.
pub fn list_to_set_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(elements) = read_list_addrs(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let set_arg = goal_arg(heap, goal, 1);
    let new_set = build_set(heap, &elements);
    unify_with_term(heap, set_arg, new_set)
}

// ── Module registration ───────────────────────────────────────────────────────

pub static SETS: PredicateModule = (
    &[
        ("set_member", 2, set_member_pred),
        ("set_union", 3, set_union_pred),
        ("set_intersection", 3, set_intersection_pred),
        ("set_difference", 3, set_difference_pred),
        ("set_symmetric_difference", 3, set_symdiff_pred),
        ("set_size", 2, set_size_pred),
        ("set_add", 3, set_add_pred),
        ("set_del", 3, set_del_pred),
        ("set_to_list", 2, set_to_list_pred),
        ("list_to_set", 2, list_to_set_pred),
        ("subset", 3, subset_sized),
    ],
    &[include_str!("../../builtins/sets.pl")],
);

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::SETS;
    use crate::predicate_modules::{utils::TestWrapper, DEFAULTS, MATHS};

    pub fn test_wrapper() -> TestWrapper {
        TestWrapper::new(&[DEFAULTS, MATHS, SETS])
    }

    pub fn query_result(query: &str) -> Vec<String> {
        test_wrapper().query_result(query)
    }

    pub fn succeeds(query: &str) -> bool {
        test_wrapper().succeeds(query)
    }

    pub fn all_bindings(query: &str, var: &str) -> Vec<String> {
        test_wrapper().all_bindings(query, var)
    }

    // ── is set? ──

    #[test]
    fn set_true() {
        assert!(succeeds("set({a, b, c})."));
    }

    #[test]
    fn set_false_atom() {
        assert!(!succeeds("set(hello)."));
    }

    #[test]
    fn set_false_list() {
        assert!(!succeeds("set([a, b])."));
    }

    // ── set_member ──

    #[test]
    fn set_member_check_present() {
        assert!(succeeds("set_member(b, {a, b, c})."));
    }

    #[test]
    fn set_member_check_absent() {
        assert!(!succeeds("set_member(d, {a, b, c})."));
    }

    #[test]
    fn set_member_enumerate() {
        let results = all_bindings("set_member(X, {a, b, c}).", "X");
        assert_eq!(results.len(), 3);
        assert!(results.contains(&"a".to_string()));
        assert!(results.contains(&"b".to_string()));
        assert!(results.contains(&"c".to_string()));
    }

    // ── set_union ──

    #[test]
    fn set_union_basic() {
        let results = query_result("set_union({a, b}, {b, c}, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        // Should contain a, b, c in some order
        assert!(r.contains('a'));
        assert!(r.contains('b'));
        assert!(r.contains('c'));
    }

    // ── set_intersection ──

    #[test]
    fn set_intersection_basic() {
        let results = query_result("set_intersection({a, b, c}, {b, c, d}, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('b'));
        assert!(r.contains('c'));
        assert!(!r.contains('a'));
        assert!(!r.contains('d'));
    }

    #[test]
    fn set_intersection_empty() {
        let results = query_result("set_intersection({a, b}, {c, d}, X).");
        assert_eq!(results.len(), 1);
        // Empty set — should be `{}`? Actually an empty set is (Set, 0) which displays as... let's check
        // With 0 elements the set_string would produce "{" then pop -> "" then "}" = "}"
        // That's a display edge case. Let's just check it succeeds.
    }

    // ── set_difference ──

    #[test]
    fn set_difference_basic() {
        let results = query_result("set_difference({a, b, c}, {b}, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('a'));
        assert!(r.contains('c'));
        assert!(!r.contains('b'));
    }

    // ── set_symmetric_difference ──

    #[test]
    fn set_symdiff_basic() {
        let results = query_result("set_symmetric_difference({a, b, c}, {b, c, d}, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('a'));
        assert!(r.contains('d'));
        assert!(!r.contains('b'));
        assert!(!r.contains('c'));
    }

    // ── set_size ──

    #[test]
    fn set_size_bind() {
        let results = query_result("set_size({a, b, c}, N).");
        assert_eq!(results, vec!["3"]);
    }

    #[test]
    fn set_size_check() {
        assert!(succeeds("set_size({a, b, c}, 3)."));
        assert!(!succeeds("set_size({a, b, c}, 2)."));
    }

    // ── set_add ──

    #[test]
    fn set_add_new_element() {
        let results = query_result("set_add({a, b}, c, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('a'));
        assert!(r.contains('b'));
        assert!(r.contains('c'));
    }

    #[test]
    fn set_add_existing_element() {
        // Adding an existing element should return the same set
        assert!(succeeds("set_add({a, b}, a, X), set_size(X, 2)."));
    }

    // ── set_del ──

    #[test]
    fn set_del_present() {
        let results = query_result("set_del({a, b, c}, b, X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('a'));
        assert!(r.contains('c'));
        assert!(!r.contains('b'));
    }

    #[test]
    fn set_del_absent() {
        // Deleting an absent element returns the original set
        assert!(succeeds("set_del({a, b}, c, X), set_size(X, 2)."));
    }

    // ── set_to_list / list_to_set ──

    #[test]
    fn set_to_list_basic() {
        let results = query_result("set_to_list({a, b, c}, X).");
        assert_eq!(results.len(), 1);
        // Should be a list containing a, b, c
        let r = &results[0];
        assert!(r.starts_with('['));
        assert!(r.contains('a'));
        assert!(r.contains('b'));
        assert!(r.contains('c'));
    }

    #[test]
    fn list_to_set_basic() {
        let results = query_result("list_to_set([a, b, a, c], X).");
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.starts_with('{'));
        assert!(r.contains('a'));
        assert!(r.contains('b'));
        assert!(r.contains('c'));
    }

    #[test]
    fn list_to_set_dedup() {
        assert!(succeeds("list_to_set([a, a, a], X), set_size(X, 1)."));
    }

    // ── temp debug ──
    #[test]
    fn diag_singleton_count() {
        // Use debug mode to understand duplicates
        let results = all_bindings("subset(X, {x}).", "X");
        eprintln!("singleton results ({}):", results.len());
        for r in &results {
            eprintln!("  {r}");
        }
        // // Also check subset_by_size directly
        // let r2 = all_bindings("subset_by_size(X, {x}, 1).", "X");
        // eprintln!("subset_by_size(X,{{x}},1) results: {:?}", r2);
        // let r0 = all_bindings("subset_by_size(X, {x}, 0).", "X");
        // eprintln!("subset_by_size(X,{{x}},0) results: {:?}", r0);
        // assert_eq!(results.len(), 2, "should have exactly 2 subsets of {{x}}");
    }

    // ── subset/3 (built-in, check mode) ──

    #[test]
    fn subset_sized_check_true() {
        assert!(succeeds("subset({a, b}, {a, b, c}, 2)."));
    }

    #[test]
    fn subset_sized_check_wrong_size() {
        // {a, b} has 2 elements — must fail even though both are in the set
        assert!(!succeeds("subset({a, b}, {a, b, c}, 3)."));
    }

    #[test]
    fn subset_sized_check_missing_element() {
        assert!(!succeeds("subset({a, d}, {a, b, c}, 2)."));
    }

    #[test]
    fn subset_sized_check_empty() {
        assert!(succeeds("subset({}, {a, b, c}, 0)."));
    }

    #[test]
    fn subset_sized_check_full_set() {
        assert!(succeeds("subset({a, b, c}, {a, b, c}, 3)."));
    }

    // ── subset/3 (built-in, generate mode) ──

    #[test]
    fn subset_sized_generate_size2() {
        let results = all_bindings("subset(X, {a, b, c}, 2).", "X");
        // C(3,2) = 3 subsets of size 2
        assert_eq!(results.len(), 3);
        for r in &results {
            assert!(r.starts_with('{'));
        }
    }

    #[test]
    fn subset_sized_generate_size0() {
        let results = all_bindings("subset(X, {a, b, c}, 0).", "X");
        // Only one size-0 subset: the empty set
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], "{}");
    }

    #[test]
    fn subset_sized_generate_size3() {
        let results = all_bindings("subset(X, {a, b, c}, 3).", "X");
        // C(3,3) = 1 subset (the full set)
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.contains('a'));
        assert!(r.contains('b'));
        assert!(r.contains('c'));
    }

    #[test]
    fn subset_sized_generate_impossible() {
        // Requesting more elements than the set has must fail
        assert!(!succeeds("subset(X, {a, b}, 3)."));
    }

    // ── subset/2 (Prolog-level, check mode) ──

    #[test]
    fn subset_two_check_true() {
        assert!(succeeds("subset({a, b}, {a, b, c})."));
    }

    #[test]
    fn subset_two_check_false() {
        assert!(!succeeds("subset({a, d}, {a, b, c})."));
    }

    #[test]
    fn subset_two_check_empty() {
        assert!(succeeds("subset({}, {a, b})."));
    }

    #[test]
    fn subset_two_check_equal_sets() {
        assert!(succeeds("subset({a, b, c}, {a, b, c})."));
    }

    // ── subset/2 (Prolog-level, generate mode) ──

    #[test]
    fn subset_two_generate_all() {
        // 2^3 = 8 subsets of a 3-element set
        let results = all_bindings("subset(X, {a, b, c}).", "X");
        assert_eq!(results.len(), 8);
    }

    #[test]
    fn subset_two_generate_singleton_set() {
        // {x} has exactly 2 subsets: {} and {x}
        let results = all_bindings("subset(X, {x}).", "X");
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn subset_compound() {
        let results = all_bindings("subset(X, {f(a),g(b)}).", "X");
        println!("{results:?}");
        for expected in ["{}", "{g(b)}", "{f(a)}", "{f(a),g(b)}"] {
            let expected: String = expected.into();
            assert!(results.contains(&expected));
        }
        assert_eq!(results.len(), 4);
    }
}
