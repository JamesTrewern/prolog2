//! Building blocks for writing native predicates.
//!
//! A predicate function receives the heap address of the goal it is resolving
//! and returns a [`PredReturn`](crate::predicate_modules::PredReturn). The helpers here cover the three things
//! almost every one of them has to do:
//!
//! 1. **Read the arguments.** [`goal_arg`](crate::predicate_modules::utils::goal_arg) gives the address of an argument,
//!    and [`resolve_to_cell`](crate::predicate_modules::utils::resolve_to_cell) follows any variable binding to the cell that
//!    actually holds the value.
//! 2. **Build a result**, with [`push_int`](crate::predicate_modules::utils::push_int) and friends for atomic values or
//!    the `build_*` functions for lists, tuples, sets and compounds.
//! 3. **Unify the result with an output argument.** A Prolog argument may
//!    arrive unbound (to be filled in) or already bound (to be checked), and
//!    the same predicate has to handle both. The `unify_with_*` functions do
//!    that, so a predicate rarely needs to match on the argument itself.
//!
//! A predicate computing the length of something looks like:
//!
//! ```ignore
//! let text = read_text(heap, goal_arg(heap, goal, 0))?;
//! unify_with_int(heap, goal_arg(heap, goal, 1), text.chars().count() as isize)
//! ```
//!
//! Nothing here allocates on the heap unless its name says so (`push_*`,
//! `build_*`), and every address returned points at a term's first cell.

use std::sync::Arc;

use crate::{
    heap::{Cell, Heap, QueryHeap, SymbolDB, Tag::*, VarBind, EMPTY_LIS, LIS},
    predicate_modules::PredReturn,
};

/// Handle possible dereferencing of ref cells return the Cell value
/// If addr is not a ref cell simply return `heap[addr]`
pub fn resolve_to_cell(heap: &QueryHeap, addr: usize) -> Cell {
    if let (Var, var_id) = heap[addr] {
        match heap.var_deref(var_id) {
            VarBind::VarId(var_id) => (Var, var_id),
            VarBind::Addr(addr) => heap[addr],
        }
    } else {
        heap[addr]
    }
}

/// Handle possible dereferencing of ref cells returning cell and address.
/// In the case of dereferencing to variable the original addr is returned
/// but may not point to ref cell with same variable ID.
/// If addr is not a ref cell simply return `(heap[addr],addr)`
pub fn resolve_to_cell_and_addr(heap: &QueryHeap, addr: usize) -> (Cell, usize) {
    if let (Var, var_id) = heap[addr] {
        match heap.var_deref(var_id) {
            VarBind::VarId(var_id) => ((Var, var_id), addr),
            VarBind::Addr(addr) => (heap[addr], addr),
        }
    } else {
        (heap[addr], addr)
    }
}

/// Dereferenced heap address of the nth argument (0-indexed) of `goal`.
pub fn goal_arg(heap: &QueryHeap, goal: usize, n: usize) -> usize {
    let mut arg_addr = goal + 2;
    for _ in 0..n {
        arg_addr += heap.term_len(arg_addr)
    }
    arg_addr
}

/// True if `addr` holds an unbound variable (self-referential `Ref`).
pub fn is_var(heap: &QueryHeap, addr: usize) -> bool {
    matches!(heap[addr], (Var, r) if r == addr)
}

// ---------------------------------------------------------------------------
// Cell conversion for embedding a term inside a new structure.
//
// When building a compound, list, or set from element addresses, most cells
// can be copied verbatim. The exception is Comp/Tup/Set — these are
// multi-cell structures and must be referenced via a `(Str, addr)` cell
// rather than copied directly. Str indirection is followed so that the
// result always points to the actual header cell.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// List reading
// ---------------------------------------------------------------------------

/// Read a list, returning element addresses and the tail address.
/// For a proper list the tail will point to an `ELis` cell.
/// For a partial list like `[a, b | T]` the tail will point to `T`.
/// Element addresses are dereferenced.
pub fn read_list_with_tail(heap: &QueryHeap, mut addr: usize) -> (Vec<usize>, usize) {
    let mut result = Vec::new();
    while LIS == heap[addr] {
        result.push(addr + 1);
        addr += heap.term_len(addr + 1) + 1;
    }
    (result, addr)
}

/// Read a proper list and return element addresses.
/// Returns `None` for partial / improper lists.
pub fn read_list_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    let (elements, tail) = read_list_with_tail(heap, addr);
    match heap[tail] {
        EMPTY_LIS => Some(elements),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Structure reading (Comp / Tup / Set)
// ---------------------------------------------------------------------------

/// The child addresses of a `Comp`, `Tup` or `Set`, or `None` for anything
/// else.
///
/// For a `Comp` the first address is the functor, as in
/// [`build_compound`]. Any variable binding on `addr` itself is
/// followed first, so this works on an argument straight out of
/// [`goal_arg`].
pub fn read_structure_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    let (cell, addr) = resolve_to_cell_and_addr(heap, addr);
    match cell.0 {
        Comp | Tup | Set => Some(heap.str_args(addr)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Reading atomic values
// ---------------------------------------------------------------------------

/// The text of a `Con` (atom) or `Stri` (string) cell, or `None` for anything
/// else.
///
/// Accepts either representation, so a predicate that works on text does not
/// need to care which one it was handed.
pub fn read_text(heap: &QueryHeap, addr: usize) -> Option<Arc<str>> {
    match resolve_to_cell(heap, addr) {
        (Con, id) => Some(SymbolDB::get_const(id)),
        (Stri, idx) => Some(SymbolDB::get_string(idx)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Pushing atomic terms
//
// Each returns the address of the cell it pushed, ready to hand to a
// `unify_with_*` function or to embed in a structure.
// ---------------------------------------------------------------------------

/// Intern `text` as an atom and push a `Con` cell for it.
pub fn push_const(heap: &mut QueryHeap, text: &str) -> usize {
    let id = SymbolDB::set_const(text);
    heap.heap_push((Con, id))
}

/// Intern `text` as a string and push a `Stri` cell for it.
pub fn push_string(heap: &mut QueryHeap, text: Arc<str>) -> usize {
    let idx = SymbolDB::set_string(text.to_string());
    heap.heap_push((Stri, idx))
}

/// Push an `Int` cell.
pub fn push_int(heap: &mut QueryHeap, value: isize) -> usize {
    heap.heap_push((Int, value as usize))
}

/// Push an `Flt` cell.
pub fn push_float(heap: &mut QueryHeap, value: f64) -> usize {
    heap.heap_push((Flt, unsafe { std::mem::transmute_copy(&value) }))
}

// ---------------------------------------------------------------------------
// Unifying a result with an output argument
//
// An output argument may arrive unbound, in which case the predicate should
// bind it, or already bound, in which case the predicate should check it.
// Every predicate that produces a value has to handle both, so these do it
// once rather than at each call site.
// ---------------------------------------------------------------------------

/// Unify `arg` with the term at `value`.
///
/// Binds `arg` if it is an unbound variable, and compares structurally if it
/// already holds a term. Use this when the result is a structure or is
/// already on the heap; the variants below avoid pushing a cell that a
/// comparison would only throw away.
pub fn unify_with_term(heap: &mut QueryHeap, arg: usize, value: usize) -> PredReturn {
    match resolve_to_cell(heap, arg) {
        (Var, var_id) => PredReturn::bind_addr(heap, var_id, value),
        _ => heap.term_equal(arg, value).into(),
    }
}

/// Unify `arg` with an integer, pushing a cell only if `arg` is unbound.
pub fn unify_with_int(heap: &mut QueryHeap, arg: usize, value: isize) -> PredReturn {
    match resolve_to_cell(heap, arg) {
        (Var, var_id) => {
            let addr = push_int(heap, value);
            PredReturn::bind_addr(heap, var_id, addr)
        }
        (Int, held) => (held as isize == value).into(),
        _ => PredReturn::False,
    }
}

/// Unify `arg` with an atom, pushing a cell only if `arg` is unbound.
pub fn unify_with_const(heap: &mut QueryHeap, arg: usize, text: &str) -> PredReturn {
    match resolve_to_cell(heap, arg) {
        (Var, var_id) => {
            let addr = push_const(heap, text);
            PredReturn::bind_addr(heap, var_id, addr)
        }
        (Con, id) => (&*SymbolDB::get_const(id) == text).into(),
        _ => PredReturn::False,
    }
}

/// Unify `arg` with a string, pushing a cell only if `arg` is unbound.
pub fn unify_with_string(heap: &mut QueryHeap, arg: usize, text: Arc<str>) -> PredReturn {
    match resolve_to_cell(heap, arg) {
        (Var, var_id) => {
            let addr = push_string(heap, text);
            PredReturn::bind_addr(heap, var_id, addr)
        }
        (Stri, idx) => (SymbolDB::get_string(idx) == text).into(),
        _ => PredReturn::False,
    }
}

// ---------------------------------------------------------------------------
// Building structures
// ---------------------------------------------------------------------------

/// Something that can be written onto the heap as one term.
///
/// This is what lets the `build_*` functions below take their elements in
/// whichever form the caller already has, rather than offering a separate
/// function per form. It is implemented for:
///
/// - [`Cell`] — a single cell, for atomic values such as a `Con` or `Int`.
/// - `usize` — the address of a term already on the heap, which is copied.
/// - `[Cell]` — a term already laid out as cells, copied verbatim.
///
/// A blanket impl covers references, so `&[&[Cell]]` works as an element
/// slice just as `&[Cell]` and `&[usize]` do.
///
/// Implement it for your own type if you have another representation to
/// build from; [`QueryHeap::heap_push`](crate::heap::Heap::heap_push) is the
/// primitive to write with.
pub trait HeapTerm {
    /// Append this term's cells to the heap.
    ///
    /// The term starts at the heap length observed before the call.
    fn push_to_heap(&self, heap: &mut QueryHeap);
}

impl HeapTerm for Cell {
    fn push_to_heap(&self, heap: &mut QueryHeap) {
        heap.heap_push(*self);
    }
}

/// An address is copied, so the built structure owns its elements rather
/// than pointing into terms that may be truncated on backtracking.
impl HeapTerm for usize {
    fn push_to_heap(&self, heap: &mut QueryHeap) {
        heap.copy_term(*self);
    }
}

impl HeapTerm for [Cell] {
    fn push_to_heap(&self, heap: &mut QueryHeap) {
        heap.cells.extend_from_slice(self);
    }
}

impl<T: HeapTerm + ?Sized> HeapTerm for &T {
    fn push_to_heap(&self, heap: &mut QueryHeap) {
        (**self).push_to_heap(heap)
    }
}

/// Build a proper list and return the address of its first cell.
///
/// An empty slice yields the empty list.
pub fn build_list(heap: &mut QueryHeap, elements: &[impl HeapTerm]) -> usize {
    let list_start = heap.heap_len();
    for element in elements {
        heap.heap_push(LIS);
        element.push_to_heap(heap);
    }
    heap.heap_push(EMPTY_LIS);
    list_start
}

/// Build a `Comp` and return the address of its `(Comp, arity)` header.
///
/// The first element is the functor, which must be a single `Con` cell; the
/// rest are its arguments.
pub fn build_compound(heap: &mut QueryHeap, parts: &[impl HeapTerm]) -> usize {
    let header = heap.heap_push((Comp, parts.len()));
    for part in parts {
        part.push_to_heap(heap);
    }
    header
}

/// Build a `Tup` and return the address of its `(Tup, len)` header.
pub fn build_tuple(heap: &mut QueryHeap, elements: &[impl HeapTerm]) -> usize {
    let header = heap.heap_push((Tup, elements.len()));
    for element in elements {
        element.push_to_heap(heap);
    }
    header
}

/// Build a `Set` and return the address of its `(Set, len)` header.
///
/// Duplicates are dropped, compared structurally. Because an element's shape
/// is only known once it is on the heap, each is written and then compared
/// against those already kept, and a duplicate is rolled back off the heap.
/// The header's length is patched once the survivors are known.
pub fn build_set(heap: &mut QueryHeap, elements: &[impl HeapTerm]) -> usize {
    let header = heap.heap_push((Set, 0));

    let mut kept: Vec<usize> = Vec::with_capacity(elements.len());
    for element in elements {
        let before = heap.heap_point();
        let addr = heap.heap_len();
        element.push_to_heap(heap);

        if kept.iter().any(|&existing| heap.term_equal(addr, existing)) {
            heap.truncate(before);
        } else {
            kept.push(addr);
        }
    }

    heap[header] = (Set, kept.len());
    header
}

// ---------------------------------------------------------------------------
// Test support
//
// Compiled only for tests: a query-driving wrapper used by the predicate
// modules' own test submodules. It is not part of the crate's API.
// ---------------------------------------------------------------------------

#[cfg(test)]
use crate::{app::App, app::Solution, predicate_modules::PredicateModule, Config};

#[cfg(test)]
pub struct TestWrapper {
    pub app: App,
}

#[cfg(test)]
impl TestWrapper {
    pub fn new(modules: &[PredicateModule]) -> Self {
        let mut config = Config::default();
        config.debug = true;
        TestWrapper {
            app: modules
                .iter()
                .fold(App::new().config(config), |app, predicate_module| {
                    app.load_module(predicate_module).unwrap()
                }),
        }
    }

    pub fn query_result(&self, query: &str) -> Vec<String> {
        let mut session = self.app.query_session(query).unwrap();
        let mut results = Vec::new();
        while let Some(solution) = session.next() {
            for (_var, val) in &solution.bindings {
                results.push(val.clone());
            }
        }
        results
    }

    pub fn succeeds(&self, query: &str) -> bool {
        let mut session = self.app.query_session(query).unwrap();
        session.next().is_some()
    }

    pub fn all_bindings(&self, query: &str, var: &str) -> Vec<String> {
        let mut session = self.app.query_session(query).unwrap();
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

    pub fn binding(&self, query: &str, var: &str) -> Option<String> {
        self.app
            .query_session(query)
            .expect("query should parse")
            .next()
            .and_then(|sol| {
                println!("{:?}", sol.bindings);
                sol.bindings
                    .into_iter()
                    .find(|(n, _)| n.as_ref() == var)
                    .map(|(_, v)| v)
            })
    }

    pub fn assert_bindings(&self, query: &str, expected_bindings: &[(&str, &str)]) {
        let solutions: Vec<Solution> = self.app.query_session(query).unwrap().collect();
        for expected in expected_bindings {
            println!("Test for binding: {} = {}", expected.0, expected.1);
            assert!(solutions.iter().any(|solution| solution
                .bindings
                .iter()
                .any(|binding| *binding.0 == *expected.0 && binding.1 == expected.1)))
        }
    }

    pub fn assert_binding(&self, query: &str, expected: (&str, &str)) {
        let solution = self.app.query_session(query).unwrap().next().unwrap();
        println!("{:?}", solution.bindings);
        assert!(solution
            .bindings
            .iter()
            .any(|binding| *binding.0 == *expected.0 && binding.1 == expected.1))
    }

    pub fn assert_false(&self, query: &str) {
        assert!(self.app.query_session(query).unwrap().next().is_none())
    }

    pub fn assert_true(&self, query: &str) {
        assert!(self.app.query_session(query).unwrap().next().is_some())
    }
}

#[cfg(test)]
mod build_tests {
    use super::*;
    use crate::heap::{Cell, QueryHeap, SymbolDB};

    fn heap() -> QueryHeap<'static> {
        QueryHeap::new(&[], None)
    }

    fn con_cell(name: &str) -> Cell {
        (Con, SymbolDB::set_const(name))
    }

    /// `f(a)` laid out as the cells of a finished term.
    fn compound_cells() -> Vec<Cell> {
        vec![(Comp, 2), con_cell("f"), con_cell("a")]
    }

    #[test]
    fn a_list_can_be_built_from_cells() {
        let mut heap = heap();
        let list = build_list(&mut heap, &[con_cell("a"), con_cell("b")]);
        assert_eq!(heap.term_string(list), "[a,b]");
    }

    #[test]
    fn a_list_can_be_built_from_addresses() {
        let mut heap = heap();
        let a = push_const(&mut heap, "a");
        let b = push_const(&mut heap, "b");
        let list = build_list(&mut heap, &[a, b]);
        assert_eq!(heap.term_string(list), "[a,b]");
    }

    /// The `[Cell]` impl, reached through the blanket impl for references, is
    /// what allows an element that is itself several cells.
    #[test]
    fn a_list_can_be_built_from_prebuilt_terms() {
        let mut heap = heap();
        let term = compound_cells();
        let list = build_list(&mut heap, &[term.as_slice(), term.as_slice()]);
        assert_eq!(heap.term_string(list), "[f(a),f(a)]");
    }

    #[test]
    fn an_empty_list_is_the_empty_list() {
        let mut heap = heap();
        let list = build_list(&mut heap, &[] as &[Cell]);
        assert_eq!(heap.term_string(list), "[]");
    }

    #[test]
    fn a_compound_takes_its_functor_first() {
        let mut heap = heap();
        let comp = build_compound(&mut heap, &[con_cell("f"), con_cell("a"), con_cell("b")]);
        assert_eq!(heap.term_string(comp), "f(a,b)");
    }

    #[test]
    fn a_tuple_holds_its_elements() {
        let mut heap = heap();
        let tuple = build_tuple(&mut heap, &[con_cell("a"), con_cell("b")]);
        assert_eq!(heap.term_string(tuple), "(a,b)");
    }

    /// Two addresses holding the same atom are distinct addresses but the
    /// same term, so only one survives.
    #[test]
    fn a_set_drops_duplicate_atoms() {
        let mut heap = heap();
        let first_a = push_const(&mut heap, "a");
        let b = push_const(&mut heap, "b");
        let second_a = push_const(&mut heap, "a");

        let set = build_set(&mut heap, &[first_a, b, second_a]);
        assert_eq!(heap.term_string(set), "{a,b}");
    }

    /// The interesting case for the rollback: a duplicate that occupies more
    /// than one cell has to be removed from the heap in full, and the header
    /// must still report the surviving count.
    #[test]
    fn a_set_drops_duplicate_compound_terms() {
        let mut heap = heap();
        let term = compound_cells();

        let set = build_set(
            &mut heap,
            &[term.as_slice(), term.as_slice(), term.as_slice()],
        );
        assert_eq!(heap.term_string(set), "{f(a)}");

        // Header plus exactly one copy of `f(a)`: nothing from the rolled
        // back duplicates is left behind.
        assert_eq!(heap.heap_len(), set + 1 + term.len());
    }

    #[test]
    fn a_set_of_distinct_terms_keeps_all_of_them() {
        let mut heap = heap();
        let set = build_set(&mut heap, &[con_cell("a"), con_cell("b"), con_cell("c")]);
        assert_eq!(heap.term_string(set), "{a,b,c}");
    }
}
