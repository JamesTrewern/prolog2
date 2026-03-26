//! Built-in string and atom predicates.
//!
//! Prolog² treats atoms (`'hello'`) and strings (`"hello"`) as distinct cell
//! types that share the same underlying text.  This module provides predicates
//! for inspecting, converting, and manipulating both.
//!
//! Atoms are interned constants (`Tag::Con`); strings are heap-indexed string
//! literals (`Tag::Stri`).  Most predicates accept either type for input
//! arguments, always producing the "natural" output type for the predicate
//! (e.g. `atom_concat` always produces an atom, `string_concat` always
//! produces a string).

use std::sync::Arc;

use super::{PredReturn, PredicateModule};
use crate::{
    Config,
    heap::{
        heap::{Heap, Tag},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    program::{hypothesis::Hypothesis, predicate_table::PredicateTable},
};

// ── Internal helpers ──────────────────────────────────────────────────────────

/// Resolve any `Str` indirection and return the functor's base address.
fn func_addr(heap: &QueryHeap, goal: usize) -> usize {
    match heap[goal] {
        (Tag::Str, ptr) => ptr,
        _ => goal,
    }
}

/// Dereferenced heap address of the nth argument (0-indexed) of `goal`.
fn arg(heap: &QueryHeap, goal: usize, n: usize) -> usize {
    heap.deref_addr(func_addr(heap, goal) + 2 + n)
}

/// Read the text of a `Con` or `Stri` cell, or `None` for anything else.
fn read_text(heap: &QueryHeap, addr: usize) -> Option<Arc<str>> {
    match heap[addr] {
        (Tag::Con, id) => Some(SymbolDB::get_const(id)),
        (Tag::Stri, idx) => Some(SymbolDB::get_string(idx)),
        _ => None,
    }
}

/// True if `addr` holds an unbound variable (self-referential `Ref`).
fn is_var(heap: &QueryHeap, addr: usize) -> bool {
    matches!(heap[addr], (Tag::Ref, r) if r == addr)
}

/// Push a fresh atom (`Con`) cell and return its heap address.
fn push_atom(heap: &mut QueryHeap, text: &str) -> usize {
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

/// Push a list of heap cells onto the heap.
///
/// Returns the address of the leading `(Lis, …)` cell, or an `(ELis, 0)` cell
/// address for an empty list.  Uses the same forward-building idiom as
/// `lists::sort`.
fn push_list<I: IntoIterator<Item = (Tag, usize)>>(heap: &mut QueryHeap, cells: I) -> usize {
    let cells: Vec<_> = cells.into_iter().collect();
    if cells.is_empty() {
        return heap.heap_push((Tag::ELis, 0));
    }
    let list_addr = heap.heap_push((Tag::Lis, heap.heap_len() + 1));
    for cell in cells {
        heap.heap_push(cell);
        heap.heap_push((Tag::Lis, heap.heap_len() + 1));
    }
    *heap.heap_last() = (Tag::ELis, 0);
    list_addr
}

/// Read a proper list of cells starting at heap address `addr`.
/// Returns `None` if the term is not a proper list or contains an unbound tail.
fn read_list(heap: &QueryHeap, mut addr: usize) -> Option<Vec<(Tag, usize)>> {
    let mut elements = Vec::new();
    loop {
        match heap[addr] {
            (Tag::ELis, _) => return Some(elements),
            (Tag::Lis, ptr) => {
                elements.push(heap[heap.deref_addr(ptr)]);
                addr = heap.deref_addr(ptr + 1);
            }
            _ => return None,
        }
    }
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

// ── Type-checking predicates ──────────────────────────────────────────────────

/// `atom/1`: succeeds if the argument is a bound atom (constant symbol).
pub fn atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    matches!(heap[arg(heap, goal, 0)], (Tag::Con, _)).into()
}

/// `string/1`: succeeds if the argument is a bound string literal.
pub fn string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    matches!(heap[arg(heap, goal, 0)], (Tag::Stri, _)).into()
}

/// `number/1`: succeeds if the argument is a bound integer or float.
pub fn number_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    matches!(heap[arg(heap, goal, 0)], (Tag::Int, _) | (Tag::Flt, _)).into()
}

/// `integer/1`: succeeds if the argument is a bound integer.
pub fn integer_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    matches!(heap[arg(heap, goal, 0)], (Tag::Int, _)).into()
}

/// `float/1`: succeeds if the argument is a bound float.
pub fn float_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    matches!(heap[arg(heap, goal, 0)], (Tag::Flt, _)).into()
}

// ── Conversion predicates ─────────────────────────────────────────────────────

/// `atom_string/2`: convert between an atom and a string.
///
/// Modes:
/// - `atom_string(+Atom, -String)` — produce the string form of an atom.
/// - `atom_string(-Atom, +String)` — produce the atom form of a string.
/// - `atom_string(+Atom, +String)` — check that their texts are identical.
pub fn atom_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let atom_a = arg(heap, goal, 0);
    let str_a  = arg(heap, goal, 1);
    match (heap[atom_a], heap[str_a]) {
        ((Tag::Con, id), (Tag::Stri, idx)) =>
            (SymbolDB::get_const(id) == SymbolDB::get_string(idx)).into(),
        ((Tag::Con, id), (Tag::Ref, r)) => {
            let result = push_string(heap, SymbolDB::get_const(id));
            PredReturn::Success(vec![(r, result)], vec![])
        }
        ((Tag::Ref, r), (Tag::Stri, idx)) => {
            let result = push_atom(heap, &SymbolDB::get_string(idx));
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => PredReturn::False,
    }
}

/// `atom_number/2`: convert between an atom and a number.
///
/// Modes:
/// - `atom_number(+Atom, -Number)` — parse the atom's text as a number.
/// - `atom_number(-Atom, +Number)` — format the number as an atom.
/// - `atom_number(+Atom, +Number)` — check consistency.
pub fn atom_number_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let atom_a = arg(heap, goal, 0);
    let num_a  = arg(heap, goal, 1);
    match (heap[atom_a], heap[num_a]) {
        // atom → number
        ((Tag::Con, id), (Tag::Ref, r)) => {
            let text = SymbolDB::get_const(id);
            match parse_and_push_number(heap, &text) {
                Some(result) => PredReturn::Success(vec![(r, result)], vec![]),
                None => PredReturn::False,
            }
        }
        // number → atom
        ((Tag::Ref, r), (Tag::Int, _) | (Tag::Flt, _)) => {
            let text = number_to_string(heap, num_a).unwrap();
            let result = push_atom(heap, &text);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        // check
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
    let num_a = arg(heap, goal, 0);
    let str_a = arg(heap, goal, 1);
    match (heap[num_a], heap[str_a]) {
        // number → string
        ((Tag::Int, _) | (Tag::Flt, _), (Tag::Ref, r)) => {
            let text = number_to_string(heap, num_a).unwrap();
            let result = push_string(heap, text.into());
            PredReturn::Success(vec![(r, result)], vec![])
        }
        // string → number
        ((Tag::Ref, r), (Tag::Stri, idx)) => {
            let text = SymbolDB::get_string(idx);
            match parse_and_push_number(heap, &text) {
                Some(result) => PredReturn::Success(vec![(r, result)], vec![]),
                None => PredReturn::False,
            }
        }
        // check
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
/// Only `term_string(+Term, -String)` is supported; the reverse (parsing a
/// string back into a term) requires a full parser and is not implemented.
pub fn term_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let term_a = arg(heap, goal, 0);
    let str_a  = arg(heap, goal, 1);
    let (Tag::Ref, r) = heap[str_a] else { return PredReturn::False; };
    let text = heap.term_string(term_a);
    let result = push_string(heap, text.into());
    PredReturn::Success(vec![(r, result)], vec![])
}

/// `char_code/2`: bidirectional conversion between a single-character atom and
/// its Unicode code point (an integer).
///
/// Modes:
/// - `char_code(+Char, -Code)`
/// - `char_code(-Char, +Code)`
/// - `char_code(+Char, +Code)` — check
pub fn char_code_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let char_a = arg(heap, goal, 0);
    let code_a = arg(heap, goal, 1);

    /// Extract a single `char` from a single-character atom, or `None`.
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
        // char → code
        ((Tag::Con, _), (Tag::Ref, r)) => match single_char(heap, char_a) {
            Some(c) => {
                let result = push_int(heap, c as isize);
                PredReturn::Success(vec![(r, result)], vec![])
            }
            None => PredReturn::False,
        },
        // code → char
        ((Tag::Ref, r), (Tag::Int, v)) => match char::from_u32(v as u32) {
            Some(c) => {
                let s: String = c.into();
                let result = push_atom(heap, &s);
                PredReturn::Success(vec![(r, result)], vec![])
            }
            None => PredReturn::False,
        },
        // check
        ((Tag::Con, _), (Tag::Int, v)) => match single_char(heap, char_a) {
            Some(c) => (c as usize == v).into(),
            None => PredReturn::False,
        },
        _ => PredReturn::False,
    }
}

// ── Length predicates ─────────────────────────────────────────────────────────

/// `atom_length/2`: length (in characters) of an atom's name.
///
/// - `atom_length(+Atom, -N)` — bind N.
/// - `atom_length(+Atom, +N)` — check.
pub fn atom_length_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let atom_a = arg(heap, goal, 0);
    let len_a  = arg(heap, goal, 1);
    let (Tag::Con, id) = heap[atom_a] else { return PredReturn::False; };
    let len = SymbolDB::get_const(id).chars().count();
    match heap[len_a] {
        (Tag::Ref, r) => {
            let result = push_int(heap, len as isize);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        (Tag::Int, v) => (len == v).into(),
        _ => PredReturn::False,
    }
}

/// `string_length/2`: length (in characters) of a string.
///
/// - `string_length(+String, -N)` — bind N.
/// - `string_length(+String, +N)` — check.
pub fn string_length_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    let str_a = arg(heap, goal, 0);
    let len_a = arg(heap, goal, 1);
    let (Tag::Stri, idx) = heap[str_a] else { return PredReturn::False; };
    let len = SymbolDB::get_string(idx).chars().count();
    match heap[len_a] {
        (Tag::Ref, r) => {
            let result = push_int(heap, len as isize);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        (Tag::Int, v) => (len == v).into(),
        _ => PredReturn::False,
    }
}

// ── Concatenation predicates ──────────────────────────────────────────────────

/// Shared logic for `atom_concat` / `string_concat`.
///
/// `make_result` converts the final text into the correct heap cell type.
fn concat_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let a = arg(heap, goal, 0);
    let b = arg(heap, goal, 1);
    let c = arg(heap, goal, 2);

    let a_text = read_text(heap, a);
    let b_text = read_text(heap, b);
    let c_text = read_text(heap, c);

    match (a_text, b_text, c_text) {
        // A ++ B → C
        (Some(at), Some(bt), None) if is_var(heap, c) => {
            let (Tag::Ref, r) = heap[c] else { return PredReturn::False; };
            let concat = format!("{at}{bt}");
            let result = make_result(heap, &concat);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        // All bound: check
        (Some(at), Some(bt), Some(ct)) => {
            let concat = format!("{at}{bt}");
            (concat.as_str() == ct.as_ref()).into()
        }
        // C - A = B (strip prefix from C)
        (Some(at), None, Some(ct)) if is_var(heap, b) => {
            let (Tag::Ref, r) = heap[b] else { return PredReturn::False; };
            match ct.strip_prefix(at.as_ref()) {
                Some(suffix) => {
                    let result = make_result(heap, suffix);
                    PredReturn::Success(vec![(r, result)], vec![])
                }
                None => PredReturn::False,
            }
        }
        // C - B = A (strip suffix from C)
        (None, Some(bt), Some(ct)) if is_var(heap, a) => {
            let (Tag::Ref, r) = heap[a] else { return PredReturn::False; };
            match ct.strip_suffix(bt.as_ref()) {
                Some(prefix) => {
                    let result = make_result(heap, prefix);
                    PredReturn::Success(vec![(r, result)], vec![])
                }
                None => PredReturn::False,
            }
        }
        _ => PredReturn::False,
    }
}

/// `atom_concat/3`: concatenate or split atoms.
///
/// Modes:
/// - `atom_concat(+A, +B, -C)` — `C` is the concatenation of `A` and `B`.
/// - `atom_concat(+A, -B, +C)` — `B` is `C` with the prefix `A` stripped.
/// - `atom_concat(-A, +B, +C)` — `A` is `C` with the suffix `B` stripped.
/// - `atom_concat(+A, +B, +C)` — check.
///
/// The result is always an atom.  Input arguments may be atoms or strings.
pub fn atom_concat_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    concat_impl(heap, goal, |h, s| push_atom(h, s))
}

/// `string_concat/3`: concatenate or split strings.
///
/// Identical to [`atom_concat_pred`] but always produces a string (`Stri`).
pub fn string_concat_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    concat_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Case-conversion predicates ────────────────────────────────────────────────

fn upcase_impl(heap: &mut QueryHeap, goal: usize, string_mode: bool) -> PredReturn {
    let in_a  = arg(heap, goal, 0);
    let out_a = arg(heap, goal, 1);
    let Some(text) = read_text(heap, in_a) else { return PredReturn::False; };
    let upper: String = text.to_uppercase();
    match heap[out_a] {
        (Tag::Ref, r) => {
            let result = if string_mode {
                push_string(heap, upper.into())
            } else {
                push_atom(heap, &upper)
            };
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => match read_text(heap, out_a) {
            Some(existing) => (existing.as_ref() == upper.as_str()).into(),
            None => PredReturn::False,
        },
    }
}

fn downcase_impl(heap: &mut QueryHeap, goal: usize, string_mode: bool) -> PredReturn {
    let in_a  = arg(heap, goal, 0);
    let out_a = arg(heap, goal, 1);
    let Some(text) = read_text(heap, in_a) else { return PredReturn::False; };
    let lower: String = text.to_lowercase();
    match heap[out_a] {
        (Tag::Ref, r) => {
            let result = if string_mode {
                push_string(heap, lower.into())
            } else {
                push_atom(heap, &lower)
            };
            PredReturn::Success(vec![(r, result)], vec![])
        }
        _ => match read_text(heap, out_a) {
            Some(existing) => (existing.as_ref() == lower.as_str()).into(),
            None => PredReturn::False,
        },
    }
}

/// `upcase_atom/2`: convert an atom to upper case.
/// - `upcase_atom(+Atom, -Upper)` / `upcase_atom(+Atom, +Upper)` — check.
pub fn upcase_atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn { upcase_impl(heap, goal, false) }

/// `downcase_atom/2`: convert an atom to lower case.
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
///
/// Forward: text → list of single-character atoms.
/// Reverse: list of single-character atoms → text (as an atom or string).
fn chars_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let text_a = arg(heap, goal, 0);
    let list_a = arg(heap, goal, 1);

    match (read_text(heap, text_a), is_var(heap, list_a)) {
        // Forward: text → char list
        (Some(text), true) => {
            let (Tag::Ref, r) = heap[list_a] else { return PredReturn::False; };
            let cells: Vec<_> = text.chars().map(|c| {
                let id = SymbolDB::set_const(c.to_string());
                (Tag::Con, id)
            }).collect();
            let list_addr = push_list(heap, cells);
            PredReturn::Success(vec![(r, list_addr)], vec![])
        }
        // Reverse: char list → text
        (None, _) if is_var(heap, text_a) => {
            let (Tag::Ref, r) = heap[text_a] else { return PredReturn::False; };
            let Some(cells) = read_list(heap, list_a) else { return PredReturn::False; };
            let mut buf = String::new();
            for (tag, v) in cells {
                let Tag::Con = tag else { return PredReturn::False; };
                let name = SymbolDB::get_const(v);
                let mut iter = name.chars();
                match (iter.next(), iter.next()) {
                    (Some(c), None) => buf.push(c),
                    _ => return PredReturn::False,
                }
            }
            let result = make_result(heap, &buf);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        // Check: both bound
        (Some(text), false) => {
            let Some(cells) = read_list(heap, list_a) else { return PredReturn::False; };
            let chars: Vec<char> = text.chars().collect();
            if chars.len() != cells.len() {
                return PredReturn::False;
            }
            for (c, (tag, v)) in chars.into_iter().zip(cells) {
                let Tag::Con = tag else { return PredReturn::False; };
                let name = SymbolDB::get_const(v);
                let mut iter = name.chars();
                match (iter.next(), iter.next()) {
                    (Some(c2), None) if c2 == c => {}
                    _ => return PredReturn::False,
                }
            }
            PredReturn::True
        }
        _ => PredReturn::False,
    }
}

/// `atom_chars/2`: convert between an atom and a list of single-character atoms.
///
/// - `atom_chars('hello', Cs)` → `Cs = [h, e, l, l, o]`
/// - `atom_chars(A, [h, i])` → `A = hi`
pub fn atom_chars_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    chars_impl(heap, goal, |h, s| push_atom(h, s))
}

/// `string_chars/2`: convert between a string and a list of single-character atoms.
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
    let text_a = arg(heap, goal, 0);
    let list_a = arg(heap, goal, 1);

    match (read_text(heap, text_a), is_var(heap, list_a)) {
        // Forward: text → code list
        (Some(text), true) => {
            let (Tag::Ref, r) = heap[list_a] else { return PredReturn::False; };
            let cells: Vec<_> = text.chars().map(|c| (Tag::Int, c as usize)).collect();
            let list_addr = push_list(heap, cells);
            PredReturn::Success(vec![(r, list_addr)], vec![])
        }
        // Reverse: code list → text
        (None, _) if is_var(heap, text_a) => {
            let (Tag::Ref, r) = heap[text_a] else { return PredReturn::False; };
            let Some(cells) = read_list(heap, list_a) else { return PredReturn::False; };
            let mut buf = String::new();
            for (tag, v) in cells {
                let Tag::Int = tag else { return PredReturn::False; };
                match char::from_u32(v as u32) {
                    Some(c) => buf.push(c),
                    None => return PredReturn::False,
                }
            }
            let result = make_result(heap, &buf);
            PredReturn::Success(vec![(r, result)], vec![])
        }
        // Check: both bound
        (Some(text), false) => {
            let Some(cells) = read_list(heap, list_a) else { return PredReturn::False; };
            let chars: Vec<char> = text.chars().collect();
            if chars.len() != cells.len() {
                return PredReturn::False;
            }
            for (c, (tag, v)) in chars.into_iter().zip(cells) {
                let Tag::Int = tag else { return PredReturn::False; };
                if c as usize != v {
                    return PredReturn::False;
                }
            }
            PredReturn::True
        }
        _ => PredReturn::False,
    }
}

/// `atom_codes/2`: convert between an atom and a list of Unicode code points.
///
/// - `atom_codes('hi', Cs)` → `Cs = [104, 105]`
/// - `atom_codes(A, [104, 105])` → `A = hi`
pub fn atom_codes_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    codes_impl(heap, goal, |h, s| push_atom(h, s))
}

/// `string_codes/2`: convert between a string and a list of Unicode code points.
pub fn string_codes_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    codes_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Substring predicates ──────────────────────────────────────────────────────

/// Shared logic for `sub_atom` / `sub_string`.
///
/// Supported modes (all others return `false`):
/// - All five arguments bound — **check** mode: verify the sub-term appears at
///   exactly the given position.
/// - `+Whole, +Before, +Length, ?After, ?Sub` — **extract** mode: compute the
///   sub-term starting at `Before` with `Length` characters, and bind `After`
///   and `Sub`.
/// - `+Whole, ?Before, ?Length, ?After, +Sub` — **find-first** mode: locate
///   the first occurrence of `Sub` and bind `Before`, `Length`, `After`.
fn sub_impl(
    heap: &mut QueryHeap,
    goal: usize,
    make_result: fn(&mut QueryHeap, &str) -> usize,
) -> PredReturn {
    let whole_a  = arg(heap, goal, 0);
    let before_a = arg(heap, goal, 1);
    let length_a = arg(heap, goal, 2);
    let after_a  = arg(heap, goal, 3);
    let sub_a    = arg(heap, goal, 4);

    let Some(whole_text) = read_text(heap, whole_a) else { return PredReturn::False; };
    let total_chars: Vec<char> = whole_text.chars().collect();
    let total = total_chars.len();

    // Extract mode: Whole + Before + Length are all bound.
    let before_val = match heap[before_a] {
        (Tag::Int, v) => Some(v),
        _ => None,
    };
    let length_val = match heap[length_a] {
        (Tag::Int, v) => Some(v),
        _ => None,
    };
    let sub_text = read_text(heap, sub_a);

    if let (Some(before), Some(length)) = (before_val, length_val) {
        if before + length > total {
            return PredReturn::False;
        }
        let sub_str: String = total_chars[before..before + length].iter().collect();
        let after = total - before - length;

        // Check mode: all five bound.
        if !is_var(heap, sub_a) && !is_var(heap, after_a) {
            let after_ok = matches!(heap[after_a], (Tag::Int, v) if v == after);
            let sub_ok = sub_text.map_or(false, |t| t.as_ref() == sub_str.as_str());
            return (after_ok && sub_ok).into();
        }

        let mut bindings = Vec::new();

        if is_var(heap, sub_a) {
            let (Tag::Ref, r) = heap[sub_a] else { return PredReturn::False; };
            bindings.push((r, make_result(heap, &sub_str)));
        } else if sub_text.map_or(true, |t| t.as_ref() != sub_str.as_str()) {
            return PredReturn::False;
        }

        if is_var(heap, after_a) {
            let (Tag::Ref, r) = heap[after_a] else { return PredReturn::False; };
            bindings.push((r, push_int(heap, after as isize)));
        } else if !matches!(heap[after_a], (Tag::Int, v) if v == after) {
            return PredReturn::False;
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
                let (Tag::Ref, r) = heap[before_a] else { return PredReturn::False; };
                bindings.push((r, push_int(heap, before as isize)));
            } else if !matches!(heap[before_a], (Tag::Int, v) if v == before) {
                return PredReturn::False;
            }
            if is_var(heap, length_a) {
                let (Tag::Ref, r) = heap[length_a] else { return PredReturn::False; };
                bindings.push((r, push_int(heap, length as isize)));
            } else if !matches!(heap[length_a], (Tag::Int, v) if v == length) {
                return PredReturn::False;
            }
            if is_var(heap, after_a) {
                let (Tag::Ref, r) = heap[after_a] else { return PredReturn::False; };
                bindings.push((r, push_int(heap, after as isize)));
            } else if !matches!(heap[after_a], (Tag::Int, v) if v == after) {
                return PredReturn::False;
            }
            return PredReturn::Success(bindings, vec![]);
        }
        return PredReturn::False;
    }

    PredReturn::False
}

/// `sub_atom/5`: extract or check a sub-atom.
///
/// `sub_atom(+Whole, ?Before, ?Length, ?After, ?Sub)`
///
/// `Before + Length + After = atom_length(Whole)`.
///
/// Supported modes:
/// - `+Whole, +Before, +Length, ?After, ?Sub` — extract sub-atom at position.
/// - `+Whole, ?Before, ?Length, ?After, +Sub` — find first occurrence of Sub.
/// - All five bound — check.
pub fn sub_atom_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    sub_impl(heap, goal, |h, s| push_atom(h, s))
}

/// `sub_string/5`: extract or check a sub-string.
///
/// Identical to [`sub_atom_pred`] but produces a string result.
pub fn sub_string_pred(
    heap: &mut QueryHeap, _: &mut Hypothesis, goal: usize, _: &PredicateTable, _: Config,
) -> PredReturn {
    sub_impl(heap, goal, |h, s| push_string(h, Arc::from(s)))
}

// ── Module registration ───────────────────────────────────────────────────────

/// Built-in string and atom predicates.
pub static STRINGS: PredicateModule = (
    &[
        // Type checks
        ("atom",    1, atom_pred),
        ("string",  1, string_pred),
        ("number",  1, number_pred),
        ("integer", 1, integer_pred),
        ("float",   1, float_pred),
        // Conversion
        ("atom_string",  2, atom_string_pred),
        ("atom_number",  2, atom_number_pred),
        ("number_string", 2, number_string_pred),
        ("term_string",  2, term_string_pred),
        ("char_code",    2, char_code_pred),
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
    use crate::app::App;
    use super::STRINGS;

    fn strings_app() -> App {
        App::new().load_module(&STRINGS).expect("STRINGS module should always load")
    }

    fn binding(query: &str, var: &str) -> Option<String> {
        strings_app()
            .query_session(query).expect("query should parse")
            .next_solution()
            .and_then(|sol| {
                sol.bindings.into_iter().find(|(n, _)| n.as_ref() == var).map(|(_, v)| v)
            })
    }

    fn succeeds(query: &str) -> bool {
        strings_app()
            .query_session(query).expect("query should parse")
            .next_solution().is_some()
    }

    // ── Type checks ───────────────────────────────────────────────────────────

    #[test]
    fn type_atom() {
        assert!(succeeds("atom(hello)."));
        // Single quotes force const interpretation even for names that look numeric.
        assert!(succeeds("atom('42')."));
        assert!(!succeeds("atom(42)."));
        assert!(!succeeds("atom(\"hello\")."));
    }

    #[test]
    fn type_string() {
        assert!(succeeds("string(\"hello\")."));
        assert!(!succeeds("string(hello)."));
        assert!(!succeeds("string(42)."));
    }

    #[test]
    fn type_number() {
        assert!(succeeds("number(42)."));
        assert!(succeeds("number(3.14)."));
        assert!(!succeeds("number(hello)."));
    }

    #[test]
    fn type_integer() {
        assert!(succeeds("integer(42)."));
        assert!(!succeeds("integer(3.14)."));
    }

    #[test]
    fn type_float() {
        assert!(succeeds("float(3.14)."));
        assert!(!succeeds("float(42)."));
    }

    // ── atom_string/2 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_string_forward() {
        // Strings display with their surrounding quote delimiters.
        assert_eq!(binding("atom_string(hello, S).", "S").as_deref(), Some("\"hello\""));
    }

    #[test]
    fn atom_string_backward() {
        assert_eq!(binding("atom_string(A, \"world\").", "A").as_deref(), Some("world"));
    }

    #[test]
    fn atom_string_check() {
        assert!(succeeds("atom_string(hello, \"hello\")."));
        assert!(!succeeds("atom_string(hello, \"world\")."));
    }

    // ── atom_number/2 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_number_forward() {
        assert_eq!(binding("atom_number('42', N).", "N").as_deref(), Some("42"));
        assert_eq!(binding("atom_number('3.14', N).", "N").as_deref(), Some("3.14"));
    }

    #[test]
    fn atom_number_backward() {
        assert_eq!(binding("atom_number(A, 42).", "A").as_deref(), Some("42"));
    }

    // ── number_string/2 ───────────────────────────────────────────────────────

    #[test]
    fn number_string_forward() {
        assert_eq!(binding("number_string(42, S).", "S").as_deref(), Some("\"42\""));
    }

    #[test]
    fn number_string_backward() {
        assert_eq!(binding("number_string(N, \"42\").", "N").as_deref(), Some("42"));
    }

    // ── term_string/2 ─────────────────────────────────────────────────────────

    #[test]
    fn term_string_atom() {
        assert_eq!(binding("term_string(hello, S).", "S").as_deref(), Some("\"hello\""));
    }

    #[test]
    fn term_string_number() {
        assert_eq!(binding("term_string(42, S).", "S").as_deref(), Some("\"42\""));
    }

    // ── char_code/2 ───────────────────────────────────────────────────────────

    #[test]
    fn char_code_forward() {
        assert_eq!(binding("char_code(a, C).", "C").as_deref(), Some("97"));
    }

    #[test]
    fn char_code_backward() {
        assert_eq!(binding("char_code(Ch, 65).", "Ch").as_deref(), Some("A"));
    }

    #[test]
    fn char_code_check() {
        assert!(succeeds("char_code(a, 97)."));
        assert!(!succeeds("char_code(a, 98)."));
    }

    // ── atom_length/2 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_length_bind() {
        assert_eq!(binding("atom_length(hello, N).", "N").as_deref(), Some("5"));
        assert_eq!(binding("atom_length('', N).", "N").as_deref(), Some("0"));
    }

    #[test]
    fn atom_length_check() {
        assert!(succeeds("atom_length(hello, 5)."));
        assert!(!succeeds("atom_length(hello, 4)."));
    }

    // ── string_length/2 ───────────────────────────────────────────────────────

    #[test]
    fn string_length_bind() {
        assert_eq!(binding("string_length(\"hello\", N).", "N").as_deref(), Some("5"));
    }

    // ── atom_concat/3 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_concat_forward() {
        assert_eq!(binding("atom_concat(hello, world, X).", "X").as_deref(), Some("helloworld"));
    }

    #[test]
    fn atom_concat_strip_prefix() {
        assert_eq!(binding("atom_concat(hello, B, helloworld).", "B").as_deref(), Some("world"));
    }

    #[test]
    fn atom_concat_strip_suffix() {
        assert_eq!(binding("atom_concat(A, world, helloworld).", "A").as_deref(), Some("hello"));
    }

    #[test]
    fn atom_concat_check() {
        assert!(succeeds("atom_concat(foo, bar, foobar)."));
        assert!(!succeeds("atom_concat(foo, bar, foobaz)."));
    }

    // ── string_concat/3 ───────────────────────────────────────────────────────

    #[test]
    fn string_concat_forward() {
        assert_eq!(
            binding("string_concat(\"foo\", \"bar\", X).", "X").as_deref(),
            Some("\"foobar\""),
        );
    }

    // ── Case conversion ───────────────────────────────────────────────────────

    #[test]
    fn upcase_atom() {
        assert_eq!(binding("upcase_atom(hello, U).", "U").as_deref(), Some("HELLO"));
    }

    #[test]
    fn downcase_atom() {
        assert_eq!(binding("downcase_atom('HELLO', D).", "D").as_deref(), Some("hello"));
    }

    #[test]
    fn upcase_string() {
        assert_eq!(binding("upcase_string(\"hello\", U).", "U").as_deref(), Some("\"HELLO\""));
    }

    // ── atom_chars/2 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_chars_forward() {
        assert_eq!(
            binding("atom_chars(hi, Cs).", "Cs").as_deref(),
            Some("[h,i]"),
        );
    }

    #[test]
    fn atom_chars_backward() {
        assert_eq!(binding("atom_chars(A, [h, i]).", "A").as_deref(), Some("hi"));
    }

    #[test]
    fn atom_chars_empty() {
        assert_eq!(binding("atom_chars('', Cs).", "Cs").as_deref(), Some("[]"));
    }

    // ── atom_codes/2 ─────────────────────────────────────────────────────────

    #[test]
    fn atom_codes_forward() {
        assert_eq!(
            binding("atom_codes(hi, Cs).", "Cs").as_deref(),
            Some("[104,105]"),
        );
    }

    #[test]
    fn atom_codes_backward() {
        assert_eq!(binding("atom_codes(A, [104, 105]).", "A").as_deref(), Some("hi"));
    }

    // ── string_chars/2 ────────────────────────────────────────────────────────

    #[test]
    fn string_chars_forward() {
        assert_eq!(
            binding("string_chars(\"hi\", Cs).", "Cs").as_deref(),
            Some("[h,i]"),
        );
    }

    // ── sub_atom/5 ───────────────────────────────────────────────────────────

    #[test]
    fn sub_atom_check() {
        assert!(succeeds("sub_atom(abcde, 1, 3, 1, bcd)."));
        assert!(!succeeds("sub_atom(abcde, 1, 3, 1, xyz)."));
        assert!(!succeeds("sub_atom(abcde, 1, 3, 2, bcd)."));  // wrong After
    }

    #[test]
    fn sub_atom_extract() {
        assert_eq!(binding("sub_atom(abcde, 1, 3, After, Sub).", "Sub").as_deref(), Some("bcd"));
        assert_eq!(binding("sub_atom(abcde, 1, 3, After, Sub).", "After").as_deref(), Some("1"));
    }

    #[test]
    fn sub_atom_find_first() {
        assert_eq!(binding("sub_atom(abcabc, B, L, A, bc).", "B").as_deref(), Some("1"));
        assert_eq!(binding("sub_atom(abcabc, B, L, A, bc).", "L").as_deref(), Some("2"));
    }

    // ── Prolog-source predicates (from strings.pl) ────────────────────────────

    #[test]
    fn string_to_atom() {
        assert_eq!(binding("string_to_atom(\"hello\", A).", "A").as_deref(), Some("hello"));
    }

    #[test]
    fn atomic_type() {
        assert!(succeeds("atomic(hello)."));
        assert!(succeeds("atomic(42)."));
        assert!(succeeds("atomic(\"hi\")."));
    }

    #[test]
    fn atomic_list_concat_test() {
        assert_eq!(
            binding("atomic_list_concat([hello, ' ', world], R).", "R").as_deref(),
            Some("hello world"),
        );
    }
}
