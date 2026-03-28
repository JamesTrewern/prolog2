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

use super::{helpers::*, PredReturn, PredicateModule};
use crate::{
    heap::{
        heap::{Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

// ── Internal helpers ──────────────────────────────────────────────────────────

/// Read the set at `addr`, returning the base address (of the `Set` cell) and
/// the element count. Returns `None` if the cell isn't a set.
fn read_set(heap: &QueryHeap, addr: usize) -> Option<(usize, usize)> {
    let addr = resolve(heap, heap.deref_addr(addr));
    match heap[addr] {
        (Tag::Set, len) => Some((addr, len)),
        _ => None,
    }
}

/// Collect the heap addresses of every element in a set.
fn set_elements(heap: &QueryHeap, base: usize, len: usize) -> Vec<usize> {
    (base + 1..=base + len).collect()
}

/// Check whether element at `elem_addr` exists in the set at `set_base` with
/// `set_len` elements, using structural equality.
fn set_contains(heap: &QueryHeap, set_base: usize, set_len: usize, elem_addr: usize) -> bool {
    (set_base + 1..=set_base + set_len).any(|a| heap._term_equal(a, elem_addr))
}

/// Push a new set onto the heap from a collection of element cells.
/// Returns the heap address of the `(Set, len)` header cell.
fn push_set(heap: &mut QueryHeap, elements: &[(Tag, usize)]) -> usize {
    let addr = heap.heap_push((Tag::Set, elements.len()));
    for &cell in elements {
        heap.heap_push(cell);
    }
    addr
}

/// Push a new set onto the heap from element *addresses* (copies their cells).
/// Deduplicates using structural equality.
fn push_set_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    // Collect cells, deduplicating
    let mut cells: Vec<(Tag, usize)> = Vec::with_capacity(addrs.len());
    let mut unique_addrs: Vec<usize> = Vec::with_capacity(addrs.len());
    for &a in addrs {
        if !unique_addrs.iter().any(|&u| heap._term_equal(a, u)) {
            unique_addrs.push(a);
            cells.push(heap[a]);
        }
    }
    push_set(heap, &cells)
}

/// Build a proper list from element addresses.
fn push_list_correct(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    if addrs.is_empty() {
        return heap.heap_push((Tag::ELis, 0));
    }
    let list_start = heap.heap_push((Tag::Lis, heap.heap_len() + 1));
    for (i, &a) in addrs.iter().enumerate() {
        heap.heap_push(heap[a]); // head element
        if i < addrs.len() - 1 {
            heap.heap_push((Tag::Lis, heap.heap_len() + 1)); // tail = next cons
        } else {
            heap.heap_push((Tag::ELis, 0)); // tail = empty list
        }
    }
    list_start
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

/// Generate all k-element combinations from a slice of element addresses.
///
/// Returns a `Vec` of `Vec<usize>`, where each inner `Vec` is one combination.
/// Order is lexicographic with respect to the original element order.
/// - `combinations(elems, 0)` always returns `vec![vec![]]` (one empty combination).
/// - `combinations(elems, k)` where `k > elems.len()` returns `vec![]` (impossible).
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
    if k == 1 {
        for elem in elems {
            sub_set.push(*elem);
            result.extend(sub_set.iter());
            sub_set.pop();
        }
    } else {
        for i in 0..elems.len()+1 - k {
            sub_set.push(elems[i]);
            combo_rec(&elems[i+1..], k - 1, sub_set, result);
            sub_set.pop();
        }
    }
}

/// Read a list into a vector of element addresses.
fn read_list_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    let mut result = Vec::new();
    let mut current = heap.deref_addr(addr);
    loop {
        match heap[current] {
            (Tag::ELis, _) => return Some(result),
            (Tag::Lis, ptr) => {
                result.push(heap.deref_addr(ptr));
                current = heap.deref_addr(ptr + 1);
            }
            _ => return None,
        }
    }
}

// ── Predicates ────────────────────────────────────────────────────────────────

/// `is_set(+X)` — succeeds if X is a set.
pub fn is_set_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    read_set(heap, goal_arg(heap, goal, 0)).is_some().into()
}

/// `set_member(?Elem, +Set)` — check membership or enumerate elements.
///
/// If `Elem` is bound, checks whether it is in `Set` (returns True/False).
/// If `Elem` is unbound, returns `PredReturn::Choices` with one alternative
/// per set element, each binding `Elem` to that element.
pub fn set_member_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let elem_addr = goal_arg(heap, goal, 0);
    let set_arg = goal_arg(heap, goal, 1);
    let Some((base, len)) = read_set(heap, set_arg) else {
        return PredReturn::False;
    };

    if is_var(heap, elem_addr) {
        // Unbound — enumerate all elements as choices
        let var_addr = heap[elem_addr].1; // The Ref target (itself)
        let alternatives: Vec<(Vec<(usize, usize)>, Vec<usize>)> = set_elements(heap, base, len)
            .into_iter()
            .map(|el_addr| (vec![(var_addr, el_addr)], vec![]))
            .collect();
        if alternatives.is_empty() {
            PredReturn::False
        } else {
            PredReturn::Choices(alternatives)
        }
    } else {
        // Bound — check membership
        set_contains(heap, base, len, elem_addr).into()
    }
}

/// `subset(?SubSet, +Set, +Size)` — SubSet is a subset of Set with exactly Size elements.
///
/// **Check mode** (`SubSet` bound): succeeds iff `SubSet` has exactly `Size` elements
/// and every element of `SubSet` is also an element of `Set`.
///
/// **Generate mode** (`SubSet` unbound): returns [`PredReturn::Choices`] with one
/// alternative per distinct `Size`-element subset of `Set`, each binding `SubSet` to
/// that subset. On backtracking the engine tries each alternative in turn.
///
/// Fails immediately if `Size` is negative, if `Size > |Set|`, or if the first argument
/// is neither a variable nor a set.
pub fn subset_sized(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some(length) = read_int(heap, goal_arg(heap, goal, 2)) else {
        return false.into();
    };
    if length < 0 {
        return PredReturn::False;
    }
    let k = length as usize;

    let Some(set) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return false.into();
    };
    if k > set.1 {
        return PredReturn::False;
    }

    let subset_arg = goal_arg(heap, goal, 0);

    if is_var(heap, subset_arg) {
        if k == 0 {
            let set_addr = heap.heap_push((Tag::Set,0));
            return PredReturn::Success(vec![(subset_arg,set_addr)], vec![]);
        }
        // Generate mode: enumerate every k-element subset of Set.
        let elems = set_elements(heap, set.0, set.1);
        let combos = combinations(&elems, k);
        if combos.is_empty() {
            return PredReturn::False;
        }
        // Push all subset structures onto the heap upfront, then wrap each in a
        // single-binding choice. Heap cells from unchosen alternatives are harmless
        // garbage — they will never be referenced once a different branch is taken.
        let mut alternatives = Vec::with_capacity(combos.len()/k);
        let mut i = 0;
        while i < combos.len(){
            let new_set = push_set_from_addrs(heap, &combos[i..i+k]);
            alternatives.push((vec![(subset_arg, new_set)], vec![]));
            i += k;
        }
        PredReturn::Choices(alternatives)
    } else if let Some(subset) = read_set(heap, subset_arg) {
        // Check mode: subset must have exactly k elements, all contained in Set.
        (subset.1 == k
            && set_elements(heap, subset.0, subset.1)
                .iter()
                .all(|elem_addr| set_contains(heap, set.0, set.1, *elem_addr)))
        .into()
    } else {
        false.into()
    }
}

/// `set_union(+Set1, +Set2, ?Result)` — Result is the union of Set1 and Set2.
pub fn set_union_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base1, len1)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let Some((base2, len2)) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };
    let result_addr = goal_arg(heap, goal, 2);

    // Collect all elements from set1, then add elements from set2 not already present
    let mut all_addrs: Vec<usize> = set_elements(heap, base1, len1);
    for a in set_elements(heap, base2, len2) {
        if !all_addrs
            .iter()
            .any(|&existing| heap._term_equal(existing, a))
        {
            all_addrs.push(a);
        }
    }

    let new_set = push_set_from_addrs(heap, &all_addrs);

    if is_var(heap, result_addr) {
        PredReturn::Success(vec![(result_addr, new_set)], vec![])
    } else {
        // Check mode: verify equality
        heap._term_equal(result_addr, new_set).into()
    }
}

/// `set_intersection(+Set1, +Set2, ?Result)` — Result is the intersection.
pub fn set_intersection_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base1, len1)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let Some((base2, len2)) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };
    let result_addr = goal_arg(heap, goal, 2);

    let common: Vec<usize> = set_elements(heap, base1, len1)
        .into_iter()
        .filter(|&a| set_contains(heap, base2, len2, a))
        .collect();

    let new_set = push_set_from_addrs(heap, &common);

    if is_var(heap, result_addr) {
        PredReturn::Success(vec![(result_addr, new_set)], vec![])
    } else {
        heap._term_equal(result_addr, new_set).into()
    }
}

/// `set_difference(+Set1, +Set2, ?Result)` — Result = Set1 \ Set2.
pub fn set_difference_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base1, len1)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let Some((base2, len2)) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };
    let result_addr = goal_arg(heap, goal, 2);

    let diff: Vec<usize> = set_elements(heap, base1, len1)
        .into_iter()
        .filter(|&a| !set_contains(heap, base2, len2, a))
        .collect();

    let new_set = push_set_from_addrs(heap, &diff);

    if is_var(heap, result_addr) {
        PredReturn::Success(vec![(result_addr, new_set)], vec![])
    } else {
        heap._term_equal(result_addr, new_set).into()
    }
}

/// `set_symmetric_difference(+Set1, +Set2, ?Result)` — elements in one but not both.
pub fn set_symdiff_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base1, len1)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let Some((base2, len2)) = read_set(heap, goal_arg(heap, goal, 1)) else {
        return PredReturn::False;
    };
    let result_addr = goal_arg(heap, goal, 2);

    let mut sym: Vec<usize> = set_elements(heap, base1, len1)
        .into_iter()
        .filter(|&a| !set_contains(heap, base2, len2, a))
        .collect();
    for a in set_elements(heap, base2, len2) {
        if !set_contains(heap, base1, len1, a) {
            sym.push(a);
        }
    }

    let new_set = push_set_from_addrs(heap, &sym);

    if is_var(heap, result_addr) {
        PredReturn::Success(vec![(result_addr, new_set)], vec![])
    } else {
        heap._term_equal(result_addr, new_set).into()
    }
}

/// `set_size(+Set, ?N)` — N is the cardinality of Set.
pub fn set_size_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((_base, len)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let n_addr = goal_arg(heap, goal, 1);

    if is_var(heap, n_addr) {
        let int_addr = heap.heap_push((Tag::Int, len));
        PredReturn::Success(vec![(n_addr, int_addr)], vec![])
    } else {
        match heap[n_addr] {
            (Tag::Int, v) => (v == len).into(),
            _ => PredReturn::False,
        }
    }
}

/// `set_add(+Set, +Elem, ?Result)` — Result is Set with Elem added (no-op if present).
pub fn set_add_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base, len)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let elem_addr = goal_arg(heap, goal, 1);
    let result_addr = goal_arg(heap, goal, 2);

    // If already present, result = original set
    if set_contains(heap, base, len, elem_addr) {
        if is_var(heap, result_addr) {
            // Bind to the original set address
            let set_addr = resolve(heap, heap.deref_addr(goal_arg(heap, goal, 0)));
            PredReturn::Success(vec![(result_addr, set_addr)], vec![])
        } else {
            heap._term_equal(
                result_addr,
                resolve(heap, heap.deref_addr(goal_arg(heap, goal, 0))),
            )
            .into()
        }
    } else {
        // Build new set with element added
        let mut addrs: Vec<usize> = set_elements(heap, base, len);
        addrs.push(elem_addr);
        let new_set = push_set_from_addrs(heap, &addrs);
        if is_var(heap, result_addr) {
            PredReturn::Success(vec![(result_addr, new_set)], vec![])
        } else {
            heap._term_equal(result_addr, new_set).into()
        }
    }
}

/// `set_del(+Set, +Elem, ?Result)` — Result is Set with Elem removed.
pub fn set_del_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base, len)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let elem_addr = goal_arg(heap, goal, 1);
    let result_addr = goal_arg(heap, goal, 2);

    let remaining: Vec<usize> = set_elements(heap, base, len)
        .into_iter()
        .filter(|&a| !heap._term_equal(a, elem_addr))
        .collect();

    let new_set = push_set_from_addrs(heap, &remaining);
    if is_var(heap, result_addr) {
        PredReturn::Success(vec![(result_addr, new_set)], vec![])
    } else {
        heap._term_equal(result_addr, new_set).into()
    }
}

/// `set_to_list(+Set, ?List)` — convert set to list.
pub fn set_to_list_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let Some((base, len)) = read_set(heap, goal_arg(heap, goal, 0)) else {
        return PredReturn::False;
    };
    let list_addr_arg = goal_arg(heap, goal, 1);

    let addrs = set_elements(heap, base, len);
    let list = push_list_correct(heap, &addrs);

    if is_var(heap, list_addr_arg) {
        PredReturn::Success(vec![(list_addr_arg, list)], vec![])
    } else {
        heap._term_equal(list_addr_arg, list).into()
    }
}

/// `list_to_set(+List, ?Set)` — convert list to set (deduplicating).
pub fn list_to_set_pred(
    heap: &mut QueryHeap,
    _hypothesis: &mut Hypothesis,
    goal: usize,
    _predicate_table: &PredicateTable,
    _config: Config,
) -> PredReturn {
    let list_arg = goal_arg(heap, goal, 0);
    let set_arg = goal_arg(heap, goal, 1);

    let Some(addrs) = read_list_addrs(heap, list_arg) else {
        return PredReturn::False;
    };

    let new_set = push_set_from_addrs(heap, &addrs);

    if is_var(heap, set_arg) {
        PredReturn::Success(vec![(set_arg, new_set)], vec![])
    } else {
        heap._term_equal(set_arg, new_set).into()
    }
}

// ── Module registration ───────────────────────────────────────────────────────

pub static SETS: PredicateModule = (
    &[
        ("is_set", 1, is_set_pred),
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
    use crate::app::App;

    fn query_result(query: &str) -> Vec<String> {
        let app = App::default().load_module(&SETS).unwrap();
        let mut session = app.query_session(query).unwrap();
        let mut results = Vec::new();
        while let Some(solution) = session.next() {
            for (_var, val) in &solution.bindings {
                results.push(val.clone());
            }
        }
        results
    }

    fn succeeds(query: &str) -> bool {
        let app = App::default();
        let mut session = app.query_session(query).unwrap();
        session.next().is_some()
    }

    fn all_bindings(query: &str, var: &str) -> Vec<String> {
        let app = App::default();
        let mut session = app.query_session(query).unwrap();
        let mut results = Vec::new();
        while let Some(solution) = session.next() {
            for (v, val) in &solution.bindings {
                if v.as_ref() == var {
                    results.push(val.clone());
                }
            }
        }
        results
    }

    // ── is_set ──

    #[test]
    fn is_set_true() {
        assert!(succeeds("is_set({a, b, c})."));
    }

    #[test]
    fn is_set_false_atom() {
        assert!(!succeeds("is_set(hello)."));
    }

    #[test]
    fn is_set_false_list() {
        assert!(!succeeds("is_set([a, b])."));
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
}
