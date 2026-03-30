//! Built-in list predicates.
//!
//! Lists in Prolog² are singly-linked cons cells terminated by `ELis`.
//! A proper list `[a, b, c]` is stored as:
//!   `(Lis, ptr) → head | (Lis, ptr) → head | … | (ELis, 0)`
//! Partial lists like `[a | T]` have a `Ref` cell as the tail.

use std::sync::Arc;

use super::{helpers::*, maths::Number, PredReturn, PredicateModule};
use crate::{
    heap::{
        heap::{Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
    Config,
};

// ── Predicates ────────────────────────────────────────────────────────────────

/// `length(+List, ?N)` — N is the number of elements in List.
///
/// Modes:
/// - `length(+List, -N)` — count elements and bind N.
/// - `length(+List, +N)` — check that the list has exactly N elements.
///
/// Fails for partial or improper lists.
pub fn length(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    let list_a = goal_arg(heap, goal, 0);
    let len_a = goal_arg(heap, goal, 1);

    let Some(elements) = read_list_addrs(heap, list_a) else {
        return false.into();
    };
    let n = elements.len();

    match heap[len_a] {
        (Tag::Ref, r) => {
            let int_addr = heap.heap_push((Tag::Int, n));
            PredReturn::Success(vec![(r, int_addr)], vec![])
        }
        (Tag::Int, v) => (n == v).into(),
        _ => false.into(),
    }
}

/// `sort(+List, -Sorted)` — Sorted is a sorted copy of List.
///
/// All elements must be of a uniform type:
/// - `Int` / `Flt` — sorted numerically.
/// - `Con` / `Stri` — sorted lexicographically.
///
/// The output argument must be an unbound variable. Fails for mixed-type
/// lists, partial lists, or a bound output argument.
pub fn sort(
    heap: &mut QueryHeap,
    _: &mut Hypothesis,
    goal: usize,
    _: &PredicateTable,
    _: Config,
) -> PredReturn {
    let list_a = goal_arg(heap, goal, 0);
    let sorted_a = goal_arg(heap, goal, 1);

    // Output must be an unbound variable.
    let (Tag::Ref, r) = heap[sorted_a] else {
        return false.into();
    };

    let Some(element_addrs) = read_list_addrs(heap, list_a) else {
        return false.into();
    };

    if element_addrs.is_empty() {
        let empty = heap.heap_push((Tag::ELis, 0));
        return PredReturn::Success(vec![(r, empty)], vec![]);
    }

    let first_tag = heap[element_addrs[0]].0;
    match first_tag {
        Tag::Flt | Tag::Int => {
            if !element_addrs
                .iter()
                .all(|&a| matches!(heap[a].0, Tag::Flt | Tag::Int))
            {
                return false.into();
            }
            let mut indexed: Vec<(usize, Number)> = element_addrs
                .into_iter()
                .map(|a| (a, Number::from_cell(heap[a])))
                .collect();
            indexed.sort_by(|(_, n1), (_, n2)| {
                n1.partial_cmp(n2).unwrap_or(std::cmp::Ordering::Equal)
            });
            let sorted_addrs: Vec<usize> = indexed.into_iter().map(|(a, _)| a).collect();
            let list_addr = build_list_from_addrs(heap, &sorted_addrs);
            PredReturn::Success(vec![(r, list_addr)], vec![])
        }
        Tag::Stri | Tag::Con => {
            if !element_addrs
                .iter()
                .all(|&a| matches!(heap[a].0, Tag::Stri | Tag::Con))
            {
                return false.into();
            }
            let mut indexed: Vec<(usize, Arc<str>)> = element_addrs
                .into_iter()
                .map(|a| {
                    let s = match heap[a] {
                        (Tag::Stri, idx) => SymbolDB::get_string(idx),
                        (Tag::Con, id) => SymbolDB::get_const(id),
                        _ => unreachable!("sort: tag changed unexpectedly"),
                    };
                    (a, s)
                })
                .collect();
            indexed.sort_by(|(_, s1), (_, s2)| s1.cmp(s2));
            let sorted_addrs: Vec<usize> = indexed.into_iter().map(|(a, _)| a).collect();
            let list_addr = build_list_from_addrs(heap, &sorted_addrs);
            PredReturn::Success(vec![(r, list_addr)], vec![])
        }
        _ => false.into(),
    }
}

// ── Module registration ───────────────────────────────────────────────────────

pub static LISTS: PredicateModule = (
    &[("length", 2, length), ("sort", 2, sort)],
    &[include_str!("../../builtins/lists.pl")],
);

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::{
        super::{helpers::TestWrapper, DEFAULTS},
        LISTS,
    };

    fn tw() -> TestWrapper {
        TestWrapper::new(&[DEFAULTS, LISTS])
    }

    // ── length/2 ──────────────────────────────────────────────────────────

    #[test]
    fn length_bind() {
        let tw = tw();
        tw.assert_binding("length([a, b, c], N).", ("N", "3"));
        tw.assert_binding("length([], N).", ("N", "0"));
        tw.assert_binding("length([1, 2], N).", ("N", "2"));
    }

    #[test]
    fn length_check() {
        let tw = tw();
        tw.assert_true("length([a, b, c], 3).");
        tw.assert_false("length([a, b, c], 2).");
        tw.assert_false("length([a, b, c], 4).");
        tw.assert_true("length([], 0).");
    }

    #[test]
    fn length_fails_non_list() {
        let tw = tw();
        tw.assert_false("length(hello, N).");
        tw.assert_false("length(42, N).");
    }

    #[test]
    fn length_fails_partial_list() {
        let tw = tw();
        tw.assert_false("length([a|_], N).");
    }

    // ── sort/2 ────────────────────────────────────────────────────────────

    #[test]
    fn sort_integers() {
        let tw = tw();
        tw.assert_binding("sort([3, 1, 2], X).", ("X", "[1,2,3]"));
        tw.assert_binding("sort([1], X).", ("X", "[1]"));
    }

    #[test]
    fn sort_floats() {
        let tw = tw();
        tw.assert_binding("sort([3.5, 1.5, 2.5], X).", ("X", "[1.5,2.5,3.5]"));
    }

    #[test]
    fn sort_atoms() {
        let tw = tw();
        tw.assert_binding("sort([b, a, c], X).", ("X", "[a,b,c]"));
        tw.assert_binding("sort([c, b, a], X).", ("X", "[a,b,c]"));
    }

    #[test]
    fn sort_empty() {
        let tw = tw();
        tw.assert_binding("sort([], X).", ("X", "[]"));
    }

    #[test]
    fn sort_already_sorted() {
        let tw = tw();
        tw.assert_binding("sort([1, 2, 3], X).", ("X", "[1,2,3]"));
    }

    #[test]
    fn sort_fails_mixed() {
        let tw = tw();
        tw.assert_false("sort([1, a, 2], X).");
    }

    #[test]
    fn sort_fails_partial_list() {
        let tw = tw();
        tw.assert_false("sort([a|_], X).");
    }

    // ── member/2 (Prolog-defined) ─────────────────────────────────────────

    #[test]
    fn member_check() {
        let tw = tw();
        tw.assert_true("member(a, [a, b, c]).");
        tw.assert_true("member(b, [a, b, c]).");
        tw.assert_false("member(d, [a, b, c]).");
    }

    #[test]
    fn member_enumerate() {
        let tw = tw();
        let results = tw.all_bindings("member(X, [a, b, c]).", "X");
        assert_eq!(results.len(), 3);
        assert!(results.contains(&"a".to_string()));
        assert!(results.contains(&"b".to_string()));
        assert!(results.contains(&"c".to_string()));
    }
}
