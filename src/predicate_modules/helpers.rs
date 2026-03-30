use crate::{app::Solution, heap::{
    heap::{Cell, Heap, Tag},
    query_heap::QueryHeap,
}};

/// Dereferenced heap address of the nth argument (0-indexed) of `goal`.
pub fn goal_arg(heap: &QueryHeap, goal: usize, n: usize) -> usize {
    heap.deref_addr(resolve(heap, goal) + 2 + n)
}

/// True if `addr` holds an unbound variable (self-referential `Ref`).
pub fn is_var(heap: &QueryHeap, addr: usize) -> bool {
    matches!(heap[addr], (Tag::Ref, r) if r == addr)
}

/// Resolve any `Str` indirection and return the structure's base address.
pub fn resolve(heap: &QueryHeap, addr: usize) -> usize {
    match heap[addr] {
        (Tag::Str, ptr) => ptr,
        _ => addr,
    }
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

/// Return the cell to use when embedding the term at `addr` inside a new
/// structure on the heap. Derefs, follows `Str`, and wraps compound-like
/// terms in `Str` indirection.
fn cell_for_addr(heap: &QueryHeap, addr: usize) -> Cell {
    let addr = heap.deref_addr(addr);
    match heap[addr] {
        (Tag::Str, ptr) => (Tag::Str, ptr),
        (Tag::Comp | Tag::Tup | Tag::Set, _) => (Tag::Str, addr),
        cell => cell,
    }
}

// ---------------------------------------------------------------------------
// List reading
// ---------------------------------------------------------------------------

/// Read a list, returning element addresses and the tail address.
/// For a proper list the tail will point to an `ELis` cell.
/// For a partial list like `[a, b | T]` the tail will point to `T`.
/// Element addresses are dereferenced.
pub fn read_list_with_tail(heap: &QueryHeap, addr: usize) -> (Vec<usize>, usize) {
    let mut result = Vec::new();
    let mut current = heap.deref_addr(addr);
    loop {
        match heap[current] {
            (Tag::Lis, ptr) => {
                result.push(heap.deref_addr(ptr));
                current = heap.deref_addr(ptr + 1);
            }
            _ => return (result, current),
        }
    }
}

/// Read a proper list and return element addresses.
/// Returns `None` for partial / improper lists.
pub fn read_list_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    let (elements, tail) = read_list_with_tail(heap, addr);
    match heap[tail] {
        (Tag::ELis, _) => Some(elements),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Structure reading (Comp / Tup / Set)
// ---------------------------------------------------------------------------

/// Read a Comp, Tup, or Set structure and return its child addresses.
/// Each address is dereferenced. Returns `None` if `addr` does not point to
/// one of these tags.
pub fn read_structure_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    let addr = heap.deref_addr(resolve(heap, addr));
    match heap[addr].0 {
        Tag::Comp | Tag::Tup | Tag::Set => Some(
            heap.str_iterator(addr)
                .map(|a| heap.deref_addr(a))
                .collect(),
        ),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// List building
// ---------------------------------------------------------------------------

/// Build a proper list on the heap from pre-made cells.
pub fn build_list(heap: &mut QueryHeap, cells: &[Cell]) -> usize {
    if cells.is_empty() {
        return heap.heap_push((Tag::ELis, 0));
    }
    let list_start = heap.heap_push((Tag::Lis, heap.heap_len() + 1));
    for cell in cells {
        heap.heap_push(*cell);
        heap.heap_push((Tag::Lis, heap.heap_len() + 1));
    }
    *heap.cells.last_mut().unwrap() = (Tag::ELis, 0);
    list_start
}

/// Build a proper list on the heap from element addresses.
/// Addresses are dereferenced and complex terms are wrapped in `Str`
/// indirection automatically.
pub fn build_list_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let cells: Vec<Cell> = addrs.iter().map(|&a| cell_for_addr(heap, a)).collect();
    build_list(heap, &cells)
}

// ---------------------------------------------------------------------------
// Structure building (Comp / Tup / Set)
// ---------------------------------------------------------------------------

/// Build a `Comp` structure on the heap from element addresses.
/// The first address is typically the functor `Con` cell; the rest are args.
/// Returns the address of the `(Comp, arity)` header cell.
pub fn build_compound_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let header = heap.heap_push((Tag::Comp, addrs.len()));
    for &a in addrs {
        heap.heap_push(cell_for_addr(heap, a));
    }
    header
}

/// Build a `Tup` structure on the heap from element addresses.
/// Returns the address of the `(Tup, len)` header cell.
pub fn build_tuple_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let header = heap.heap_push((Tag::Tup, addrs.len()));
    for &a in addrs {
        heap.heap_push(cell_for_addr(heap, a));
    }
    header
}

/// Build a `Set` on the heap from element addresses.
/// Deduplicates using structural equality.
/// Returns the address of the `(Set, len)` header cell.
pub fn build_set_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let mut unique_addrs: Vec<usize> = Vec::with_capacity(addrs.len());
    for &a in addrs {
        if !unique_addrs.iter().any(|&u| heap.term_equal(a, u)) {
            unique_addrs.push(a);
        }
    }
    let header = heap.heap_push((Tag::Set, unique_addrs.len()));
    for &a in unique_addrs.iter() {
        heap.heap_push(cell_for_addr(heap, a));
    }
    header
}

/// Build a `Set` on the heap from pre-made cells.
pub fn build_set(heap: &mut QueryHeap, elements: &[Cell]) -> usize {
    let addr = heap.heap_push((Tag::Set, elements.len()));
    for &cell in elements {
        heap.heap_push(cell);
    }
    addr
}

use crate::{app::App, predicate_modules::PredicateModule};

pub struct TestWrapper {
    pub app: App,
}

impl TestWrapper {
    pub fn new(modules: &[PredicateModule]) -> Self {
        TestWrapper {
            app: modules.iter().fold(App::new(), |app, predicate_module| {
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
            .query_session(query).expect("query should parse")
            .next()
            .and_then(|sol| {
                sol.bindings
                    .into_iter()
                    .find(|(n, _)| n.as_ref() == var)
                    .map(|(_, v)| v)
            })
    }

    pub fn assert_bindings(&self, query: &str, expected_bindings: &[(&str, &str)]) {
        let solutions: Vec<Solution> = self.app.query_session(query).unwrap().collect();
        println!("Solution: {:?}", solutions);
        for expected in expected_bindings{
            println!("Test for binding: {} = {}", expected.0, expected.1);
            assert!(solutions.iter().any(|solution| solution.bindings.iter().any(|binding|*binding.0 == *expected.0 && binding.1 == expected.1)))
        }
    }

    pub fn assert_binding(&self, query: &str, expected: (&str, &str)) {
        let solution = self.app.query_session(query).unwrap().next().unwrap();
        assert!(solution.bindings.iter().any(|binding|*binding.0 == *expected.0 && binding.1 == expected.1))
    }

    pub fn assert_false(&self, query: &str) {
        assert!(self.app.query_session(query).unwrap().next().is_none())
    }

    pub fn assert_true(&self, query: &str) {
        assert!(self.app.query_session(query).unwrap().next().is_some())
    }
}
