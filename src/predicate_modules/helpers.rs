use crate::{
    app::Solution,
    heap::{Cell, Heap, QueryHeap, Tag::*, TermWalk, Walk, EMPTY_LIS, LIS},
    Config,
};

/// Handle possible dereferencing of ref cells return the Cell value
/// If addr is not a ref cell simply return `heap[addr]`
pub fn resolve_to_cell(heap: &QueryHeap, addr: usize) -> Cell {
    if let (Ref, var_id) = heap[addr] {
        match heap.var_deref(var_id) {
            crate::heap::VarBind::Var(var_id) => (Ref, var_id),
            crate::heap::VarBind::Addr(addr) => heap[addr],
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
    if let (Ref, var_id) = heap[addr] {
        match heap.var_deref(var_id) {
            crate::heap::VarBind::Var(var_id) => ((Ref, var_id), addr),
            crate::heap::VarBind::Addr(addr) => (heap[addr], addr),
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
    matches!(heap[addr], (Ref, r) if r == addr)
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

/// Read a Comp, Tup, or Set structure and return its child addresses.
/// Each address is dereferenced. Returns `None` if `addr` does not point to
/// one of these tags.
pub fn read_structure_addrs(heap: &QueryHeap, addr: usize) -> Option<Vec<usize>> {
    // let addr = heap.deref_addr(resolve(heap, addr));
    // match heap[addr].0 {
    //     Comp | Tup | Set => Some(
    //         heap.str_args(addr)
    //             .map(|a| heap.deref_addr(a))
    //             .collect(),
    //     ),
    //     _ => None,
    // }
    todo!()
}

// ---------------------------------------------------------------------------
// List building
// ---------------------------------------------------------------------------

/// Build a proper list on the heap from pre-made cells.
pub fn build_list_from_cells(heap: &mut QueryHeap, cells: &[Cell]) -> usize {
    if cells.is_empty() {
        return heap.heap_push(EMPTY_LIS);
    }
    let list_start = heap.heap_len();
    for cell in cells {
        heap.heap_push(LIS);
        heap.heap_push(*cell);
    }
    heap.heap_push(EMPTY_LIS);
    list_start
}

/// Build a proper list on the heap from element addresses.
/// Addresses are dereferenced and complex terms are wrapped in `Str`
/// indirection automatically.
pub fn build_list_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let list_start = heap.heap_len();
    for addr in addrs {
        heap.heap_push(LIS);
        heap.copy_term(*addr);
    }
    heap.heap_push(EMPTY_LIS);
    list_start
}

/// Build list from array of cell slices.
/// Similar to [`predicate_modules::helpers::build_list_from_cells`] but allows pre compiled complex terms
pub fn build_list_from_terms(heap: &mut QueryHeap, cells: &[&[Cell]]) -> usize {
    if cells.is_empty() {
        return heap.heap_push(EMPTY_LIS);
    }
    let list_start = heap.heap_len();
    for cells in cells {
        heap.heap_push(LIS);
        heap.cells.extend_from_slice(cells);
    }
    heap.heap_push(EMPTY_LIS);
    list_start
}

// ---------------------------------------------------------------------------
// Structure building (Comp / Tup / Set)
// ---------------------------------------------------------------------------

/// Build a `Comp` structure on the heap from element addresses.
/// The first address is the functor `Con` cell; the rest are args.
/// Undefined behaviour may occur if the functor term is complex
/// Returns the address of the `(Comp, arity)` header cell.
pub fn build_compound_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let header = heap.heap_push((Comp, addrs.len()));
    for &addr in addrs {
        heap.copy_term(addr);
    }
    header
}

/// Build a `Tup` structure on the heap from element addresses.
/// Returns the address of the `(Tup, len)` header cell.
pub fn build_tuple_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let header = heap.heap_push((Tup, addrs.len()));
    for &addr in addrs {
        heap.copy_term(addr);
    }
    header
}

/// Build a `Set` on the heap from element addresses.
/// Deduplicates using structural equality.
/// Returns the address of the `(Set, len)` header cell.
pub fn build_set_from_addrs(heap: &mut QueryHeap, addrs: &[usize]) -> usize {
    let mut unique_addrs: Vec<usize> = Vec::with_capacity(addrs.len());
    for &addr in addrs {
        if !unique_addrs.iter().any(|&u| heap.term_equal(addr, u)) {
            unique_addrs.push(addr);
        }
    }
    let header = heap.heap_push((Set, unique_addrs.len()));
    for &addr in unique_addrs.iter() {
        heap.copy_term(addr);
    }
    header
}

/// Build a `Set` on the heap from pre-made cells.
pub fn build_set_from_cells(heap: &mut QueryHeap, elements: &[Cell]) -> usize {
    let addr = heap.heap_push((Set, elements.len()));
    heap.cells.extend_from_slice(elements);
    addr
}

use crate::{app::App, predicate_modules::PredicateModule};

pub struct TestWrapper {
    pub app: App,
}

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
