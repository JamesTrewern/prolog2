//! Built-in string and atom predicates.
//!
//! Prolog² treats constants (`'hello'`) and strings (`"hello"`) as distinct
//! cell types that share the same underlying text.  This module provides
//! predicates for inspecting, converting, and manipulating both.
//!
//! Constants are interned symbols (`Tag::Con`); strings are heap-indexed
//! string literals (`Tag::Stri`).  Most predicates accept either type for
//! input arguments, always producing the "natural" output type for the
//! predicate (e.g. `atom_concat` always produces a constant, `string_concat`
//! always produces a string).

use std::sync::Arc;

use super::{helpers::*, PredReturn, PredicateModule};
use crate::{
    Config,
    heap::{
        heap::{Cell, Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
};

// ── Internal helpers ──────────────────────────────────────────────────────────

/// Read the text of a `Con` or `Stri` cell, or `None` for anything else.
fn read_text(heap: &QueryHeap, addr: usize) -> Option<Arc<str>> {
    match heap[addr] {
        (Tag::Con, id)  => Some(SymbolDB::get_const(id)),
        (Tag::Stri, idx) => Some(SymbolDB::get_string(idx)),
        _ => None,
    }
}

/// Push a fresh constant (`Con`) cell and return its heap address.
fn push_const(heap: &mut QueryHeap, text: &str) -> usize {
    let id = SymbolDB::set_const(text);
    heap.heap_push((Tag::Con, id))
}

/// Push a fresh string (`Stri`) cell and return its heap address.
fn push_string(heap: &mut QueryHeap, text: Arc<str>) -> usize {
    let idx = SymbolDB::set_string(text.to_string());
    heap.heap_push((Tag::Stri, idx))
}

/// Push an integer (`Int`) cell and return its heap address.
fn push_int(heap: &mut QueryHeap, n: isize) -> usize {
    heap.heap_push((Tag::Int, n as usize))
}

/// Read a proper list and return each element as a raw heap cell.
/// Returns `None` if the list is improper or has a variable tail.
/// Equivalent to `read_list_addrs` but yields cells directly.
fn read_list_cells(heap: &QueryHeap, addr: usize) -> Option<Vec<Cell>> {
    read_list_addrs(heap, addr).map(|addrs| addrs.iter().map(|&a| heap[a]).collect())
}

/// Parse a string as `Int` (tried first) or `Flt`, push the result, and
/// return its address, or `None` if the text is not a valid number.
fn parse_and_push_number(heap: &mut QueryHeap, s: &str) -> Option<usize> {
    if let Ok(n) = s.parse::<isize>() {
        Some(push_int(heap, n))
    } else if let Ok(f) = s.parse::<f64>() {
        Some(heap.heap_push((Tag::Flt, f.to_bits() as usize)))
    } else {
        None
    }
}

/// Format a numeric heap cell as a `String`, or `None` for non-numeric cells.
fn number_to_string(heap: &QueryHeap, addr: usize) -> Option<String> {
    match heap[addr] {
        (Tag::Int, v) => Some((v as isize).to_string()),
        (Tag::Flt, v) => Some(f64::from_bits(v as u64).to_string()),
        _ => None,
    }
}

// ── Conversion predicates ─────────────────────────────────────────────────────

/// `atom_string/2`: convert between a constant and a string.
///
/// Modes:
/// - `atom_string(+Const, -String)` — produce the string form.
/// - `atom_string(-Const, +String)` — produce the constant form.
/// - `atom_string(+Const, +String)` — check that their texts are identical.
pub fn atom_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let const_a = goal_arg(heap, goal, 0);
    let str_a   = goal_arg(heap, goal, 1);
    match (heap[const_a], heap[str_a]) {
        ((Tag::Con, id), (Tag::Stri, idx)) =>
            (SymbolDB::get_const(id) == SymbolDB::get_string(idx)).into(),
        ((Tag::Con, id), (Tag::Ref, r)) => {
            let result = push_string(heap, SymbolDB::get_const(id));
            PredReturn::Success(vec![(r, result)], vec![])
        }
        ((Tag::Ref, r), (Tag::Stri, idx)) => {
            let result = push_const(heap, &SymbolDB::get_string(idx));
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => PredReturn::False,
    }
}

/// `atom_number/2`: convert between a constant and a number.
///
/// Modes:
/// - `atom_number(+Const, -Number)` — parse the constant's text as a number.
/// - `atom_number(-Const, +Number)` — format the number as a constant.
/// - `atom_number(+Const, +Number)` — check consistency.
pub fn atom_number_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let const_a = goal_arg(heap, goal, 0);
    let num_a   = goal_arg(heap, goal, 1);
    match (heap[const_a], heap[num_a]) {
        ((Tag::Con, id), (Tag::Ref, r)) => {
            let text = SymbolDB::get_const(id);
            match parse_and_push_number(heap, &text) {
                Some(result) => PredReturn::Success(vec![(r, result)], vec![]),
                None => PredReturn::False,
            }
        }
        ((Tag::Ref, r), (Tag::Int, _) | (Tag::Flt, _)) => {
            let text = number_to_string(heap, num_a).unwrap();
            let result = push_const(heap, &text);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        ((Tag::Con, id), (Tag::Int, v)) => {
            let text = SymbolDB::get_const(id);
            text.parse::<isize>().map_or(PredReturn::False, |n| (n == v as isize).into())
        }
        ((Tag::Con, id), (Tag::Flt, v)) => {
            let text = SymbolDB::get_const(id);
            text.parse::<f64>()
                .map_or(PredReturn::False, |f| (f.to_bits() == v as u64).into())
        }
        _ => PredReturn::False,
    }
}

/// `number_string/2`: convert between a number and a string.
///
/// Modes:
/// - `number_string(+Number, -String)` — format the number as a string.
/// - `number_string(-Number, +String)` — parse the string as a number.
/// - `number_string(+Number, +String)` — check consistency.
pub fn number_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let num_a = goal_arg(heap, goal, 0);
    let str_a = goal_arg(heap, goal, 1);
    match (heap[num_a], heap[str_a]) {
        ((Tag::Int, _) | (Tag::Flt, _), (Tag::Ref, r)) => {
            let text = number_to_string(heap, num_a).unwrap();
            let result = push_string(heap, text.into());
            PredReturn::Success(vec![(r, result)], vec![])
        }
        ((Tag::Ref, r), (Tag::Stri, idx)) => {
            let text = SymbolDB::get_string(idx);
            match parse_and_push_number(heap, &text) {
                Some(result) => PredReturn::Success(vec![(r, result)], vec![]),
                None => PredReturn::False,
            }
        }
        ((Tag::Int, v), (Tag::Stri, idx)) => {
            let text = SymbolDB::get_string(idx);
            text.parse::<isize>().map_or(PredReturn::False, |n| (n == v as isize).into())
        }
        ((Tag::Flt, v), (Tag::Stri, idx)) => {
            let text = SymbolDB::get_string(idx);
            text.parse::<f64>()
                .map_or(PredReturn::False, |f| (f.to_bits() == v as u64).into())
        }
        _ => PredReturn::False,
    }
}

/// `term_string/2`: convert any ground term to its Prolog text representation.
///
/// Only `term_string(+Term, -String)` is supported.
pub fn term_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let term_a = goal_arg(heap, goal, 0);
    let str_a  = goal_arg(heap, goal, 1);
    let (Tag::Ref, r) = heap[str_a] else { return false.into(); };
    let text = heap.term_string(term_a);
    let result = push_string(heap, text.into());
    PredReturn::Success(vec![(r, result)], vec![])
}

/// `char_code/2`: bidirectional conversion between a single-character constant
/// and its Unicode code point (an integer).
///
/// Modes:
/// - `char_code(+Char, -Code)`
/// - `char_code(-Char, +Code)`
/// - `char_code(+Char, +Code)` — check
pub fn char_code_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let char_a = goal_arg(heap, goal, 0);
    let code_a = goal_arg(heap, goal, 1);

    fn single_char(heap: &QueryHeap, addr: usize) -> Option<char> {
        let (Tag::Con, id) = heap[addr] else { return None; };
        let name = SymbolDB::get_const(id);
        let mut iter = name.chars();
        match (iter.next(), iter.next()) {
            (Some(c), None) => Some(c),
            _ => None,
        }
    }

    match (heap[char_a], heap[code_a]) {
        ((Tag::Con, _), (Tag::Ref, r)) => match single_char(heap, char_a) {
            Some(c) => PredReturn::Success(vec![(r, push_int(heap, c as isize))], vec![]),
            None => PredReturn::False,
        },
        ((Tag::Ref, r), (Tag::Int, v)) => match char::from_u32(v as u32) {
            Some(c) => {
                let result = push_const(heap, &c.to_string());
                PredReturn::Success(vec![(r, result)], vec![])
            }
            None => PredReturn::False,
        },
        ((Tag::Con, _), (Tag::Int, v)) => match single_char(heap, char_a) {
            Some(c) => (c as usize == v).into(),
            None => PredReturn::False,
        },
        _ => PredReturn::False,
    }
}

// ── Length predicates ─────────────────────────────────────────────────────────

/// `atom_length/2`: length (in characters) of a constant's name.
pub fn atom_length_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let const_a = goal_arg(heap, goal, 0);
    let len_a   = goal_arg(heap, goal, 1);
    let (Tag::Con, id) = heap[const_a] else { return false.into(); };
    let len = SymbolDB::get_const(id).chars().count();
    match heap[len_a] {
        (Tag::Ref, r) => PredReturn::Success(vec![(r, push_int(heap, len as isize))], vec![]),
        (Tag::Int, v) => (len == v).into(),
        _ => PredReturn::False,
    }
}

/// `string_length/2`: length (in characters) of a string.
pub fn string_length_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let str_a = goal_arg(heap, goal, 0);
    let len_a = goal_arg(heap, goal, 1);
    let (Tag::Stri, idx) = heap[str_a] else { return false.into(); };
    let len = SymbolDB::get_string(idx).chars().count();
    match heap[len_a] {
        (Tag::Ref, r) => PredReturn::Success(vec![(r, push_int(heap, len as isize))], vec![]),
        (Tag::Int, v) => (len == v).into(),
        _ => PredReturn::False,
    }
}

// ── Concatenation predicates ──────────────────────────────────────────────────

/// Shared logic for `atom_concat` / `string_concat`.
fn concat_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let a = goal_arg(heap, goal, 0);
    let b = goal_arg(heap, goal, 1);
    let c = goal_arg(heap, goal, 2);

    let a_text = read_text(heap, a);
    let b_text = read_text(heap, b);
    let c_text = read_text(heap, c);

    match (a_text, b_text, c_text) {
        (Some(at), Some(bt), None) if is_var(heap, c) => {
            let (Tag::Ref, r) = heap[c] else { return false.into(); };
            let result = make_result(heap, &format!("{at}{bt}"));
            PredReturn::Success(vec![(r, result)], vec![])
        }
        (Some(at), Some(bt), Some(ct)) => {
            (format!("{at}{bt}").as_str() == ct.as_ref()).into()
        }
        (Some(at), None, Some(ct)) if is_var(heap, b) => {
            let (Tag::Ref, r) = heap[b] else { return false.into(); };
            match ct.strip_prefix(at.as_ref()) {
                Some(suffix) => PredReturn::Success(vec![(r, make_result(heap, suffix))], vec![]),
                None => PredReturn::False,
            }
        }
        (None, Some(bt), Some(ct)) if is_var(heap, a) => {
            let (Tag::Ref, r) = heap[a] else { return false.into(); };
            match ct.strip_suffix(bt.as_ref()) {
                Some(prefix) => PredReturn::Success(vec![(r, make_result(heap, prefix))], vec![]),
                None => PredReturn::False,
            }
        }
        _ => PredReturn::False,
    }
}

/// `atom_concat/3`: concatenate or split constants.
pub fn atom_concat_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    concat_impl(heap, goal, |h, s| push_const(h, s))
}

/// `string_concat/3`: concatenate or split strings.
pub fn string_concat_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    concat_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Case-conversion predicates ────────────────────────────────────────────────

fn upcase_impl(heap: &mut QueryHeap, goal: usize, string_mode: bool) -> PredReturn {
    let in_a  = goal_arg(heap, goal, 0);
    let out_a = goal_arg(heap, goal, 1);
    let Some(text) = read_text(heap, in_a) else { return false.into(); };
    let upper = text.to_uppercase();
    match heap[out_a] {
        (Tag::Ref, r) => {
            let result = if string_mode { push_string(heap, upper.into()) } else { push_const(heap, &upper) };
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => read_text(heap, out_a)
            .map_or(PredReturn::False, |existing| (existing.as_ref() == upper.as_str()).into()),
    }
}

fn downcase_impl(heap: &mut QueryHeap, goal: usize, string_mode: bool) -> PredReturn {
    let in_a  = goal_arg(heap, goal, 0);
    let out_a = goal_arg(heap, goal, 1);
    let Some(text) = read_text(heap, in_a) else { return false.into(); };
    let lower = text.to_lowercase();
    match heap[out_a] {
        (Tag::Ref, r) => {
            let result = if string_mode { push_string(heap, lower.into()) } else { push_const(heap, &lower) };
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => read_text(heap, out_a)
            .map_or(PredReturn::False, |existing| (existing.as_ref() == lower.as_str()).into()),
    }
}

/// `upcase_atom/2`: convert a constant to upper case.
pub fn upcase_atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn { upcase_impl(heap, goal, false) }

/// `downcase_atom/2`: convert a constant to lower case.
pub fn downcase_atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn { downcase_impl(heap, goal, false) }

/// `upcase_string/2`: convert a string to upper case.
pub fn upcase_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn { upcase_impl(heap, goal, true) }

/// `downcase_string/2`: convert a string to lower case.
pub fn downcase_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn { downcase_impl(heap, goal, true) }

// ── Character-list predicates ─────────────────────────────────────────────────

/// Shared logic for `atom_chars` / `string_chars`.
fn chars_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let text_a = goal_arg(heap, goal, 0);
    let list_a = goal_arg(heap, goal, 1);

    match (read_text(heap, text_a), is_var(heap, list_a)) {
        (Some(text), true) => {
            let (Tag::Ref, r) = heap[list_a] else { return false.into(); };
            let cells: Vec<Cell> = text.chars().map(|c| {
                (Tag::Con, SymbolDB::set_const(c.to_string()))
            }).collect();
            PredReturn::Success(vec![(r, build_list(heap, &cells))], vec![])
        }
        (None, _) if is_var(heap, text_a) => {
            let (Tag::Ref, r) = heap[text_a] else { return false.into(); };
            let Some(cells) = read_list_cells(heap, list_a) else { return false.into(); };
            let mut buf = String::new();
            for (tag, v) in cells {
                let Tag::Con = tag else { return false.into(); };
                let name = SymbolDB::get_const(v);
                let mut iter = name.chars();
                match (iter.next(), iter.next()) {
                    (Some(c), None) => buf.push(c),
                    _ => return false.into(),
                }
            }
            PredReturn::Success(vec![(r, make_result(heap, &buf))], vec![])
        }
        (Some(text), false) => {
            let Some(cells) = read_list_cells(heap, list_a) else { return false.into(); };
            let chars: Vec<char> = text.chars().collect();
            if chars.len() != cells.len() { return false.into(); }
            for (c, (tag, v)) in chars.into_iter().zip(cells) {
                let Tag::Con = tag else { return false.into(); };
                let name = SymbolDB::get_const(v);
                let mut iter = name.chars();
                match (iter.next(), iter.next()) {
                    (Some(c2), None) if c2 == c => {}
                    _ => return false.into(),
                }
            }
            PredReturn::True
        }
        _ => PredReturn::False,
    }
}

/// `atom_chars/2`: convert between a constant and a list of single-character constants.
pub fn atom_chars_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    chars_impl(heap, goal, |h, s| push_const(h, s))
}

/// `string_chars/2`: convert between a string and a list of single-character constants.
pub fn string_chars_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    chars_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

/// Shared logic for `atom_codes` / `string_codes`.
fn codes_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let text_a = goal_arg(heap, goal, 0);
    let list_a = goal_arg(heap, goal, 1);

    match (read_text(heap, text_a), is_var(heap, list_a)) {
        (Some(text), true) => {
            let (Tag::Ref, r) = heap[list_a] else { return false.into(); };
            let cells: Vec<Cell> = text.chars().map(|c| (Tag::Int, c as usize)).collect();
            PredReturn::Success(vec![(r, build_list(heap, &cells))], vec![])
        }
        (None, _) if is_var(heap, text_a) => {
            let (Tag::Ref, r) = heap[text_a] else { return false.into(); };
            let Some(cells) = read_list_cells(heap, list_a) else { return false.into(); };
            let mut buf = String::new();
            for (tag, v) in cells {
                let Tag::Int = tag else { return false.into(); };
                match char::from_u32(v as u32) {
                    Some(c) => buf.push(c),
                    None => return false.into(),
                }
            }
            PredReturn::Success(vec![(r, make_result(heap, &buf))], vec![])
        }
        (Some(text), false) => {
            let Some(cells) = read_list_cells(heap, list_a) else { return false.into(); };
            let chars: Vec<char> = text.chars().collect();
            if chars.len() != cells.len() { return false.into(); }
            for (c, (tag, v)) in chars.into_iter().zip(cells) {
                let Tag::Int = tag else { return false.into(); };
                if c as usize != v { return false.into(); }
            }
            PredReturn::True
        }
        _ => PredReturn::False,
    }
}

/// `atom_codes/2`: convert between a constant and a list of Unicode code points.
pub fn atom_codes_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    codes_impl(heap, goal, |h, s| push_const(h, s))
}

/// `string_codes/2`: convert between a string and a list of Unicode code points.
pub fn string_codes_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    codes_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Substring predicates ──────────────────────────────────────────────────────

/// Shared logic for `sub_atom` / `sub_string`.
fn sub_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let whole_a  = goal_arg(heap, goal, 0);
    let before_a = goal_arg(heap, goal, 1);
    let length_a = goal_arg(heap, goal, 2);
    let after_a  = goal_arg(heap, goal, 3);
    let sub_a    = goal_arg(heap, goal, 4);

    let Some(whole_text) = read_text(heap, whole_a) else { return false.into(); };
    let total_chars: Vec<char> = whole_text.chars().collect();
    let total = total_chars.len();

    let before_val = match heap[before_a] { (Tag::Int, v) => Some(v), _ => None };
    let length_val = match heap[length_a] { (Tag::Int, v) => Some(v), _ => None };
    let sub_text   = read_text(heap, sub_a);

    // Extract mode: Whole + Before + Length are all bound.
    if let (Some(before), Some(length)) = (before_val, length_val) {
        if before + length > total { return false.into(); }
        let sub_str: String = total_chars[before..before + length].iter().collect();
        let after = total - before - length;

        if !is_var(heap, sub_a) && !is_var(heap, after_a) {
            let after_ok = matches!(heap[after_a], (Tag::Int, v) if v == after);
            let sub_ok   = sub_text.map_or(false, |t| t.as_ref() == sub_str.as_str());
            return (after_ok && sub_ok).into();
        }

        let mut bindings = Vec::new();
        if is_var(heap, sub_a) {
            let (Tag::Ref, r) = heap[sub_a] else { return false.into(); };
            bindings.push((r, make_result(heap, &sub_str)));
        } else if sub_text.map_or(true, |t| t.as_ref() != sub_str.as_str()) {
            return false.into();
        }
        if is_var(heap, after_a) {
            let (Tag::Ref, r) = heap[after_a] else { return false.into(); };
            bindings.push((r, push_int(heap, after as isize)));
        } else if !matches!(heap[after_a], (Tag::Int, v) if v == after) {
            return false.into();
        }
        return PredReturn::Success(bindings, vec![]);
    }

    // Find-first mode: Whole + Sub are bound, position arguments unbound.
    if let Some(sub_t) = sub_text {
        if let Some(byte_pos) = whole_text.find(sub_t.as_ref()) {
            let before = whole_text[..byte_pos].chars().count();
            let length = sub_t.chars().count();
            let after  = total - before - length;

            let mut bindings = Vec::new();
            if is_var(heap, before_a) {
                let (Tag::Ref, r) = heap[before_a] else { return false.into(); };
                bindings.push((r, push_int(heap, before as isize)));
            } else if !matches!(heap[before_a], (Tag::Int, v) if v == before) {
                return false.into();
            }
            if is_var(heap, length_a) {
                let (Tag::Ref, r) = heap[length_a] else { return false.into(); };
                bindings.push((r, push_int(heap, length as isize)));
            } else if !matches!(heap[length_a], (Tag::Int, v) if v == length) {
                return false.into();
            }
            if is_var(heap, after_a) {
                let (Tag::Ref, r) = heap[after_a] else { return false.into(); };
                bindings.push((r, push_int(heap, after as isize)));
            } else if !matches!(heap[after_a], (Tag::Int, v) if v == after) {
                return false.into();
            }
            return PredReturn::Success(bindings, vec![]);
        }
        return false.into();
    }

    PredReturn::False
}

/// `sub_atom/5`: extract or check a sub-constant.
pub fn sub_atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    sub_impl(heap, goal, |h, s| push_const(h, s))
}

/// `sub_string/5`: extract or check a sub-string.
pub fn sub_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    sub_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Module registration ───────────────────────────────────────────────────────

pub static STRINGS: PredicateModule = (
    &[
        // Conversion
        ("atom_string",   2, atom_string_pred),
        ("atom_number",   2, atom_number_pred),
        ("number_string", 2, number_string_pred),
        ("term_string",   2, term_string_pred),
        ("char_code",     2, char_code_pred),
        // Length
        ("atom_length",   2, atom_length_pred),
        ("string_length", 2, string_length_pred),
        // Concatenation
        ("atom_concat",   3, atom_concat_pred),
        ("string_concat", 3, string_concat_pred),
        // Case
        ("upcase_atom",     2, upcase_atom_pred),
        ("downcase_atom",   2, downcase_atom_pred),
        ("upcase_string",   2, upcase_string_pred),
        ("downcase_string", 2, downcase_string_pred),
        // Character lists
        ("atom_chars",   2, atom_chars_pred),
        ("atom_codes",   2, atom_codes_pred),
        ("string_chars", 2, string_chars_pred),
        ("string_codes", 2, string_codes_pred),
        // Substring
        ("sub_atom",   5, sub_atom_pred),
        ("sub_string", 5, sub_string_pred),
    ],
    &[include_str!("../../builtins/strings.pl")],
);

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::{super::{DEFAULTS, helpers::TestWrapper}, STRINGS};

    /// Strings tests that also need DEFAULTS (for atomic/1, type checks, etc.)
    fn tw() -> TestWrapper {
        TestWrapper::new(&[DEFAULTS, STRINGS])
    }

    // ── atom_string/2 ─────────────────────────────────────────────────────

    #[test]
    fn atom_string_forward() {
        assert_eq!(tw().binding("atom_string(hello, S).", "S").as_deref(), Some("\"hello\""));
    }

    #[test]
    fn atom_string_backward() {
        assert_eq!(tw().binding("atom_string(A, \"world\").", "A").as_deref(), Some("world"));
    }

    #[test]
    fn atom_string_check() {
        tw().assert_true("atom_string(hello, \"hello\").");
        tw().assert_false("atom_string(hello, \"world\").");
    }

    // ── atom_number/2 ─────────────────────────────────────────────────────

    #[test]
    fn atom_number_forward() {
        assert_eq!(tw().binding("atom_number('42', N).", "N").as_deref(), Some("42"));
        assert_eq!(tw().binding("atom_number('3.14', N).", "N").as_deref(), Some("3.14"));
    }

    #[test]
    fn atom_number_backward() {
        assert_eq!(tw().binding("atom_number(A, 42).", "A").as_deref(), Some("42"));
    }

    // ── number_string/2 ───────────────────────────────────────────────────

    #[test]
    fn number_string_forward() {
        assert_eq!(tw().binding("number_string(42, S).", "S").as_deref(), Some("\"42\""));
    }

    #[test]
    fn number_string_backward() {
        assert_eq!(tw().binding("number_string(N, \"42\").", "N").as_deref(), Some("42"));
    }

    // ── term_string/2 ─────────────────────────────────────────────────────

    #[test]
    fn term_string_atom() {
        assert_eq!(tw().binding("term_string(hello, S).", "S").as_deref(), Some("\"hello\""));
    }

    #[test]
    fn term_string_number() {
        assert_eq!(tw().binding("term_string(42, S).", "S").as_deref(), Some("\"42\""));
    }

    // ── char_code/2 ───────────────────────────────────────────────────────

    #[test]
    fn char_code_forward() {
        assert_eq!(tw().binding("char_code(a, C).", "C").as_deref(), Some("97"));
    }

    #[test]
    fn char_code_backward() {
        assert_eq!(tw().binding("char_code(Ch, 65).", "Ch").as_deref(), Some("A"));
    }

    #[test]
    fn char_code_check() {
        tw().assert_true("char_code(a, 97).");
        tw().assert_false("char_code(a, 98).");
    }

    // ── atom_length/2 ─────────────────────────────────────────────────────

    #[test]
    fn atom_length_bind() {
        assert_eq!(tw().binding("atom_length(hello, N).", "N").as_deref(), Some("5"));
        assert_eq!(tw().binding("atom_length('', N).", "N").as_deref(), Some("0"));
    }

    #[test]
    fn atom_length_check() {
        tw().assert_true("atom_length(hello, 5).");
        tw().assert_false("atom_length(hello, 4).");
    }

    // ── string_length/2 ───────────────────────────────────────────────────

    #[test]
    fn string_length_bind() {
        assert_eq!(tw().binding("string_length(\"hello\", N).", "N").as_deref(), Some("5"));
    }

    // ── atom_concat/3 ─────────────────────────────────────────────────────

    #[test]
    fn atom_concat_forward() {
        assert_eq!(tw().binding("atom_concat(hello, world, X).", "X").as_deref(), Some("helloworld"));
    }

    #[test]
    fn atom_concat_strip_prefix() {
        assert_eq!(tw().binding("atom_concat(hello, B, helloworld).", "B").as_deref(), Some("world"));
    }

    #[test]
    fn atom_concat_strip_suffix() {
        assert_eq!(tw().binding("atom_concat(A, world, helloworld).", "A").as_deref(), Some("hello"));
    }

    #[test]
    fn atom_concat_check() {
        tw().assert_true("atom_concat(foo, bar, foobar).");
        tw().assert_false("atom_concat(foo, bar, foobaz).");
    }

    // ── string_concat/3 ───────────────────────────────────────────────────

    #[test]
    fn string_concat_forward() {
        assert_eq!(
            tw().binding("string_concat(\"foo\", \"bar\", X).", "X").as_deref(),
            Some("\"foobar\""),
        );
    }

    // ── Case conversion ───────────────────────────────────────────────────

    #[test]
    fn upcase_atom() {
        assert_eq!(tw().binding("upcase_atom(hello, U).", "U").as_deref(), Some("HELLO"));
    }

    #[test]
    fn downcase_atom() {
        assert_eq!(tw().binding("downcase_atom('HELLO', D).", "D").as_deref(), Some("hello"));
    }

    #[test]
    fn upcase_string() {
        assert_eq!(tw().binding("upcase_string(\"hello\", U).", "U").as_deref(), Some("\"HELLO\""));
    }

    // ── atom_chars/2 ─────────────────────────────────────────────────────

    #[test]
    fn atom_chars_forward() {
        assert_eq!(tw().binding("atom_chars(hi, Cs).", "Cs").as_deref(), Some("[h,i]"));
    }

    #[test]
    fn atom_chars_backward() {
        assert_eq!(tw().binding("atom_chars(A, [h, i]).", "A").as_deref(), Some("hi"));
    }

    #[test]
    fn atom_chars_empty() {
        assert_eq!(tw().binding("atom_chars('', Cs).", "Cs").as_deref(), Some("[]"));
    }

    // ── atom_codes/2 ─────────────────────────────────────────────────────

    #[test]
    fn atom_codes_forward() {
        assert_eq!(tw().binding("atom_codes(hi, Cs).", "Cs").as_deref(), Some("[104,105]"));
    }

    #[test]
    fn atom_codes_backward() {
        assert_eq!(tw().binding("atom_codes(A, [104, 105]).", "A").as_deref(), Some("hi"));
    }

    // ── string_chars/2 ────────────────────────────────────────────────────

    #[test]
    fn string_chars_forward() {
        assert_eq!(tw().binding("string_chars(\"hi\", Cs).", "Cs").as_deref(), Some("[h,i]"));
    }

    // ── sub_atom/5 ───────────────────────────────────────────────────────

    #[test]
    fn sub_atom_check() {
        tw().assert_true("sub_atom(abcde, 1, 3, 1, bcd).");
        tw().assert_false("sub_atom(abcde, 1, 3, 1, xyz).");
        tw().assert_false("sub_atom(abcde, 1, 3, 2, bcd).");
    }

    #[test]
    fn sub_atom_extract() {
        assert_eq!(tw().binding("sub_atom(abcde, 1, 3, After, Sub).", "Sub").as_deref(), Some("bcd"));
        assert_eq!(tw().binding("sub_atom(abcde, 1, 3, After, Sub).", "After").as_deref(), Some("1"));
    }

    #[test]
    fn sub_atom_find_first() {
        assert_eq!(tw().binding("sub_atom(abcabc, B, L, A, bc).", "B").as_deref(), Some("1"));
        assert_eq!(tw().binding("sub_atom(abcabc, B, L, A, bc).", "L").as_deref(), Some("2"));
    }

    // ── Prolog-source predicates ──────────────────────────────────────────

    #[test]
    fn string_to_atom() {
        assert_eq!(tw().binding("string_to_atom(\"hello\", A).", "A").as_deref(), Some("hello"));
    }

    #[test]
    fn atomic_type() {
        // atomic/1 is now defined in defaults.pl
        tw().assert_true("atomic(hello).");
        tw().assert_true("atomic(42).");
        tw().assert_true("atomic(\"hi\").");
        tw().assert_false("atomic(X).");
        tw().assert_false("atomic(f(x)).");
    }

    #[test]
    fn atomic_list_concat_test() {
        assert_eq!(
            tw().binding("atomic_list_concat([hello, ' ', world], R).", "R").as_deref(),
            Some("hello world"),
        );
    }
}
