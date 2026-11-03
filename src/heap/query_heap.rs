use super::{
    Cell, Heap, ProgramHeap, SymbolDB,
    Tag::*,
    TermWalk,
    VarBind::{self, *},
    VarReg, Walk,
};
use smallvec::SmallVec;
use std::{
    collections::HashMap,
    ops::{Index, IndexMut, Range, RangeFrom},
    sync::Arc,
};

/// Source names for a heap's variables, keyed by variable register id.
///
/// Sparse: only variables that came from parsed source have a name at all.
/// Everything resolution invents during a proof is unnamed and renders as
/// `Ref_<id>`, which is the common case by a wide margin.
pub(crate) type VarNames = HashMap<usize, Arc<str>>;

/// (Heap cells length, Variable registers length)
pub type HeapPoint = (usize, usize);

/// Working heap for proof search.
///
/// Wraps a shared read-only program heap (`&[Cell]`) and an
/// owned mutable cell buffer for query-time allocations. Supports
/// branching via an optional parent pointer for backtracking.
pub struct QueryHeap<'a> {
    pub(crate) cells: Vec<Cell>,
    /// The program this heap reads symbols from.
    ///
    /// Separate from `prog_cells` because the two are independent: a
    /// detached heap (see [`Self::detached`]) addresses from zero while still
    /// naming constants in the program's table.
    prog: &'a ProgramHeap,
    prog_cells: &'a [Cell],
    /// The cells of the heap this one was branched from, read-only.
    ///
    /// Addresses run `[prog_cells][root][cells]`, and `IndexMut` refuses
    /// anything below the end of `root`, so a branch can read everything its
    /// parent had allocated while writing only its own cells.
    ///
    /// Held as a plain slice rather than a pointer back to the parent heap:
    /// that is what makes a `QueryHeap` `Send`, so branches can be handed to
    /// different threads. The cost is that branches do not nest -- a branch
    /// of a branch would have two ancestors' cells to stitch together, and
    /// [`Self::branch`] rejects it.
    root: Option<&'a [Cell]>,
    pub(crate) var_regs: Vec<VarReg>, //Reference binding registers
    /// Names of variables this heap created.
    var_names: VarNames,
    /// Names of the parent's variables, for a branch that inherited its
    /// registers.
    ///
    /// `Some` only for [`Self::branch_inherit`]. Those branches clone the
    /// parent's registers, so a parent variable keeps its id in the branch
    /// and the parent's names apply unchanged; variables the branch goes on
    /// to create land above `var_regs.len()` and so cannot collide with one.
    ///
    /// `None` for [`Self::branch_ground`], whose registers start empty: its
    /// id 0 is a different variable from the parent's id 0, and inheriting
    /// names would print a fresh variable under a parent's name.
    root_var_names: Option<&'a VarNames>,
}

impl<'a> QueryHeap<'a> {
    pub fn new(prog: &'a ProgramHeap, root: Option<&'a [Cell]>) -> QueryHeap<'a> {
        QueryHeap {
            cells: Vec::new(),
            prog,
            prog_cells: prog.cells(),
            root,
            var_regs: vec![VarReg::UNBOUND; prog.max_arg()],
            var_names: VarNames::new(),
            root_var_names: None,
        }
    }

    /// A heap that shares `prog`'s symbols but none of its cells, so its own
    /// addresses start at zero.
    ///
    /// For scratch heaps whose cells are later relocated into another heap:
    /// addresses that begin at zero need no program-length offset unwound at
    /// the point of the move.
    pub(crate) fn detached(prog: &'a ProgramHeap) -> QueryHeap<'a> {
        QueryHeap {
            cells: Vec::new(),
            prog,
            prog_cells: &[],
            root: None,
            var_regs: vec![VarReg::UNBOUND; prog.max_arg()],
            var_names: VarNames::new(),
            root_var_names: None,
        }
    }

    /// `count` heaps that read this one's cells but write their own, with no
    /// variable registers of their own.
    ///
    /// **Every term a branch reads from this heap must be ground.** A `Var`
    /// cell would dereference against an empty register table, which panics
    /// rather than reading a stale binding. Callers ground what they want
    /// read first, which is cheaper than copying the registers into every
    /// branch -- so this is the right branch when the work is read-only
    /// against finished terms, as testing a grounded hypothesis against the
    /// negative examples is.
    ///
    /// Because the registers start empty, the branch's variable ids do not
    /// correspond to this heap's: its id 0 is a different variable. It
    /// therefore does not inherit variable names either -- see
    /// [`Self::branch_inherit`] for the case that does.
    ///
    /// Nothing has to be undone afterwards. A branch cannot write this
    /// heap's cells (`IndexMut` refuses them) and binds only registers it
    /// created, so dropping it leaves this heap exactly as it was.
    ///
    /// Borrows `self` for as long as the branches live, so this heap cannot
    /// allocate while they exist -- which is exactly the invariant their
    /// addresses depend on.
    pub fn branch_ground<'b>(&'b self, count: usize) -> Vec<QueryHeap<'b>> {
        self.branches(count, false)
    }

    /// `count` heaps that inherit this one's bindings and variable names.
    ///
    /// Each clones the variable registers, so a branch can read any term
    /// this heap holds, bound or not, and bind those variables for itself
    /// without the others or this heap seeing it. That is what a nested
    /// sub-proof needs: one goal explored several ways, or explored once and
    /// then discarded.
    ///
    /// Cloning the registers keeps the branch's variable ids equal to this
    /// heap's, so the inherited names stay correct and a variable parsed as
    /// `X` still prints as `X` inside the branch. New variables the branch
    /// creates sit above the inherited range and are named, or not, locally.
    ///
    /// Costs a register vector per branch, where [`Self::branch_ground`]
    /// costs nothing; prefer that one when the terms are already ground.
    ///
    /// # Panics
    ///
    /// If this heap is itself a branch; neither branch kind nests.
    pub fn branch_inherit<'b>(&'b self, count: usize) -> Vec<QueryHeap<'b>> {
        self.branches(count, true)
    }

    /// Shared construction for the two branch kinds.
    ///
    /// # Panics
    ///
    /// If this heap is itself a branch. A branch holds exactly one ancestor's
    /// cells, so a branch of a branch would have two ranges to stitch
    /// together between the program heap and its own. Lifting this needs the
    /// `root` field to become a list of ancestors, and until it does, a
    /// sub-proof that itself wants a sub-proof -- `not(not(G))` -- cannot be
    /// built on these.
    fn branches<'b>(&'b self, count: usize, inherit: bool) -> Vec<QueryHeap<'b>> {
        assert!(
            self.root.is_none(),
            "branches do not nest: this heap is already a branch"
        );
        (0..count)
            .map(|_| QueryHeap {
                cells: Vec::new(),
                prog: self.prog,
                prog_cells: self.prog_cells,
                root: Some(&self.cells),
                var_regs: if inherit {
                    self.var_regs.clone()
                } else {
                    // Not empty, unlike the cells: a branch proves goals
                    // against clause templates, so it needs the argument
                    // window even though it inherits no variables.
                    vec![VarReg::UNBOUND; self.prog.max_arg()]
                },
                var_names: VarNames::new(),
                root_var_names: inherit.then_some(&self.var_names),
            })
            .collect()
    }

    /// Duplicate term from self, tracking variable identity
    /// via `ref_map`. Unbound Ref cells in `self` are mapped to fresh Ref
    /// cells in `self`; the same source Ref always maps to the same target Ref.
    /// Call with a shared `ref_map` across multiple terms to preserve variable
    /// sharing (e.g. across literals in a clause).
    /// Used to duplicate terms from immutable cells such as prog_cells or root_heap heap
    /// and place them in mutable cells.
    pub fn dup_term(&mut self, addr: usize, ref_map: &mut HashMap<usize, usize>) {
        let mut walk = TermWalk::new(addr);
        while let Some(cell) = walk.next_cell(self) {
            if cell.0 == Var {
                if let Some(&mapped) = ref_map.get(&cell.1) {
                    self.heap_push((Var, mapped));
                } else {
                    let new_var_id = self.set_var(None);
                    ref_map.insert(cell.1, new_var_id);
                }
            } else {
                self.heap_push(cell);
            }
        }
    }

    pub fn check_constraints(&self, cons: &[usize]) -> bool {
        let derefs: SmallVec<[VarBind; 8]> =
            cons.iter().map(|var_id| self.var_deref(*var_id)).collect();
        for i in 0..cons.len() {
            for j in (i + 1)..cons.len() {
                match (derefs[i], derefs[j]) {
                    (Addr(addr1), Addr(addr2)) if self.term_equal(addr1, addr2) => return false,
                    (v1, v2) if v1 == v2 => return false,
                    _ => (),
                }
            }
        }
        true
    }

    /// Get heap point to truncate back to later upon backtracking
    pub fn heap_point(&self) -> HeapPoint {
        (self.cells.len(), self.var_regs.len())
    }

    /// Free memory no longer needed upon back tracking
    pub fn truncate(&mut self, (cells_len, var_regs_len): HeapPoint) {
        self.cells.truncate(cells_len);
        self.var_regs.truncate(var_regs_len);
    }

    /// The argument registers reserved at the front of [`Self::var_regs`].
    ///
    /// Sized from the program, so it covers the widest clause that can be
    /// resolved against. Variables created during a proof land above it.
    pub(crate) fn arg_window(&self) -> usize {
        self.prog.max_arg()
    }

    /// Create new variable register and return ID without creating cell
    pub fn new_var(&mut self, value: VarReg) -> usize {
        let var_id = self.var_regs.len();
        self.var_regs.push(value);
        var_id
    }

    pub fn _print_var_regs(&self) {
        println!("Var Regs");
        println!("------------");
        for (i, var_reg) in self.var_regs.iter().enumerate() {
            match var_reg.get_bind() {
                Some(bind) => println!("{i:3}: {bind:?}"),
                None => println!("{i:3}: UNBOUND"),
            }
        }
        println!("------------");
    }

    pub fn var_string(&self, var_id: usize) -> String {
        match self.var_name(var_id) {
            Some(symbol) => symbol.to_string(),
            None => format!("Ref_{var_id}"),
        }
    }
}

impl Heap for QueryHeap<'_> {
    fn symbols(&self) -> &SymbolDB {
        self.prog.symbols()
    }

    /// An `Arg` below the program cells is a clause template read from the
    /// program, so its parsed name comes from there. One in query space was
    /// built during a proof and has no parsed name; printing falls back to a
    /// positional one.
    fn arg_name(&self, addr: usize) -> Option<Arc<str>> {
        (addr < self.prog_cells.len())
            .then(|| self.prog.arg_name(addr))
            .flatten()
    }

    /// This heap's own names, then an inherited parent's.
    ///
    /// The two ranges are disjoint: a branch that inherited names also
    /// inherited the registers they belong to, so its own variables start
    /// above them.
    fn var_name(&self, var_id: usize) -> Option<Arc<str>> {
        self.var_names
            .get(&var_id)
            .or_else(|| self.root_var_names?.get(&var_id))
            .cloned()
    }

    fn set_var_name(&mut self, var_id: usize, symbol: Arc<str>) {
        self.var_names.insert(var_id, symbol);
    }

    fn heap_push(&mut self, cell: Cell) -> usize {
        let i = self.heap_len();
        self.cells.push(cell);
        i
    }

    fn heap_len(&self) -> usize {
        self.prog_cells.len() + self.root.map_or(0, <[Cell]>::len) + self.cells.len()
    }

    fn prog_addr(&self, addr: usize) -> bool {
        addr >= self.prog_cells.len()
    }

    fn heap_last(&mut self) -> &mut Cell {
        self.cells.last_mut().unwrap()
    }

    #[inline(always)]
    fn var_deref(&self, mut var_id: usize) -> VarBind {
        loop {
            if self.var_regs[var_id].var() {
                var_id = self.var_regs[var_id].value()
            } else {
                if self.var_regs[var_id].bound() {
                    return Addr(self.var_regs[var_id].0);
                } else {
                    return VarId(var_id);
                }
            }
        }
    }

    /// Bind variable of var_id
    /// @var_id: variable id/bindinging index
    /// @value: value to set in binding
    /// @var: is binding to another variable id or an address
    fn bind(&mut self, var_id: usize, binding: VarBind) {
        self.var_regs[var_id].bind(binding);
    }

    fn unbind(&mut self, bound_vars: &[usize]) {
        for var_id in bound_vars {
            self.var_regs[*var_id].unbind();
        }
    }

    /// Add variable cell to heap
    /// If using existing var_id simple push new cell return var_id
    /// If creating new var push unbound to var bindings array and return new index (var_id)
    fn set_var(&mut self, var_id: Option<usize>) -> usize {
        //If no address provided set addr to current heap len
        let var_id = var_id.unwrap_or({
            //Create new var id
            let var_id = self.var_regs.len();
            self.var_regs.push(VarReg::UNBOUND);
            var_id
        });

        self.heap_push((Var, var_id));
        var_id
    }

    fn bound(&self, var_id: usize) -> Option<VarBind> {
        self.var_regs[var_id].get_bind()
    }
}

impl Index<usize> for QueryHeap<'_> {
    type Output = Cell;

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.prog_cells.len() {
            return &self.prog_cells[index];
        }
        let offset = index - self.prog_cells.len();
        match self.root {
            // Parent's cells, then our own after them
            Some(root) if offset < root.len() => &root[offset],
            Some(root) => &self.cells[offset - root.len()],
            None => &self.cells[offset],
        }
    }
}

impl IndexMut<usize> for QueryHeap<'_> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.prog_cells.len() {
            unreachable!(
                "IndexMut: attempted mutable access to program heap cell at index {index}"
            );
        }
        let offset = index - self.prog_cells.len();
        let root_len = self.root.map_or(0, <[Cell]>::len);
        if offset < root_len {
            unreachable!("IndexMut: attempted mutable access to parent heap cell at index {index}");
        }
        &mut self.cells[offset - root_len]
    }
}

impl Index<Range<usize>> for QueryHeap<'_> {
    type Output = [Cell];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        let len = self.prog_cells.len();

        if index.start < len && index.end <= len {
            &self.prog_cells[index]
        } else if index.start >= len && self.root.is_none() {
            &self.cells[index.start - len..index.end - len]
        } else {
            unreachable!("Index<Range>: range {index:?} spans the static program heap and mutable query cells")
        }
    }
}

impl Index<RangeFrom<usize>> for QueryHeap<'_> {
    type Output = [Cell];

    fn index(&self, mut index: RangeFrom<usize>) -> &Self::Output {
        assert!(
            index.start >= self.prog_cells.len(),
            "Can't Index with RangeFrom in program heap space"
        );
        assert!(
            self.root.is_none(),
            "Can't Index with RangeFrom on branched heap"
        );
        index.start -= self.prog_cells.len();
        &self.cells[index]
    }
}

#[cfg(test)]
mod branch_tests {
    use super::super::{
        test_prog, Heap, QueryHeap,
        Tag::*,
        VarBind::{Addr, VarId},
    };

    /// A heap with one named, bound variable and one named, unbound one.
    fn parent(prog: &super::ProgramHeap) -> QueryHeap<'_> {
        let mut heap = QueryHeap::new(prog, None);
        let a = heap.symbols().set_const("a");
        let bound = heap.set_var(None); // var 0, cell 0
        let unbound = heap.set_var(None); // var 1, cell 1
        heap.set_var_name(bound, "X".into());
        heap.set_var_name(unbound, "Y".into());
        let a_addr = heap.heap_push((Con, a));
        heap.bind(bound, Addr(a_addr));
        heap
    }

    #[test]
    fn inherit_carries_bindings() {
        let prog = test_prog();
        let heap = parent(prog);
        let branches = heap.branch_inherit(2);

        for branch in &branches {
            assert_eq!(
                branch.var_deref(0),
                Addr(2),
                "a branch must see what the parent had already bound"
            );
            assert_eq!(branch.var_deref(1), VarId(1), "and what it had not");
        }
    }

    #[test]
    fn inherit_carries_var_names() {
        let prog = test_prog();
        let heap = parent(prog);
        let branches = heap.branch_inherit(1);

        assert_eq!(&*branches[0].var_name(0).unwrap(), "X");
        assert_eq!(&*branches[0].var_name(1).unwrap(), "Y");
    }

    #[test]
    fn a_branchs_own_variables_are_named_locally() {
        let prog = test_prog();
        let heap = parent(prog);
        let mut branches = heap.branch_inherit(1);
        let branch = &mut branches[0];

        // Above the inherited registers, so it cannot collide with X or Y.
        let fresh = branch.set_var(None);
        assert_eq!(fresh, 2);
        branch.set_var_name(fresh, "Z".into());

        assert_eq!(&*branch.var_name(fresh).unwrap(), "Z");
        assert_eq!(&*branch.var_name(0).unwrap(), "X", "inherited name intact");
    }

    #[test]
    fn a_ground_branch_inherits_neither_registers_nor_names() {
        let prog = test_prog();
        let heap = parent(prog);
        let mut branches = heap.branch_ground(1);
        let branch = &mut branches[0];

        // Its id 0 is a *different* variable from the parent's id 0, so the
        // parent's name for that id must not apply to it.
        let fresh = branch.set_var(None);
        assert_eq!(fresh, 0, "registers start empty");
        assert_eq!(
            branch.var_name(0),
            None,
            "a ground branch's fresh variable must not pick up the parent's X"
        );
        assert_eq!(branch.var_string(0), "Ref_0");
    }

    #[test]
    fn a_branch_binding_does_not_reach_the_parent() {
        let prog = test_prog();
        let heap = parent(prog);
        {
            let mut branches = heap.branch_inherit(2);
            let target = branches[0].heap_push((Con, 1));
            branches[0].bind(1, Addr(target));
            assert_eq!(branches[0].var_deref(1), Addr(target));
            assert_eq!(
                branches[1].var_deref(1),
                VarId(1),
                "and not its siblings either"
            );
        }
        assert_eq!(heap.var_deref(1), VarId(1));
    }

    #[test]
    #[should_panic(expected = "branches do not nest")]
    fn branches_do_not_nest() {
        let prog = test_prog();
        let heap = parent(prog);
        let branches = heap.branch_inherit(1);
        let _ = branches[0].branch_ground(1);
    }
}

#[cfg(test)]
mod dup_term_tests {
    use super::super::{test_prog, Heap, QueryHeap, Tag::*};
    use std::collections::HashMap;

    /// The same source variable must map to one fresh variable.
    ///
    /// This is the property the `ref_map` exists for, and the one a key
    /// mismatch between its insert and its lookup silently broke: every
    /// occurrence then minted a new variable, so `f(X,X)` duplicated as
    /// `f(A,B)` and two positions that had to agree no longer did.
    #[test]
    fn repeated_variables_stay_shared() {
        let prog = test_prog();
        let mut heap = QueryHeap::new(prog, None);
        let f = heap.symbols().set_const("f");

        // Deliberately make the variable's id differ from the term's
        // address. With them equal -- the natural first thing to write, `X`
        // as var 0 in a term at address 0 -- a lookup keyed on the address
        // instead of the id coincides with the right answer, and the test
        // passes while sharing is broken.
        for _ in 0..3 {
            heap.new_var(super::VarReg::UNBOUND);
        }
        let x = heap.new_var(super::VarReg::UNBOUND);
        assert_ne!(x, 0, "the point of the padding above");

        // f(X, X) with X unbound, laid out by hand.
        heap.cells.extend([(Comp, 3), (Con, f), (Var, x), (Var, x)]);

        let src = 0;
        let copy = heap.heap_len();
        heap.dup_term(src, &mut HashMap::new());

        let cells = &heap[copy..];
        assert_eq!(cells.len(), 4, "a copy is the same shape as its source");
        assert_eq!(cells[0], (Comp, 3));
        assert_eq!(cells[1], (Con, f));
        assert_eq!(
            cells[2], cells[3],
            "both occurrences must be the same fresh variable"
        );
        assert_ne!(cells[2], (Var, x), "and it must be fresh, not the original");
    }

    /// A shared `ref_map` keeps variables shared across separate calls, which
    /// is how the literals of one clause stay connected.
    #[test]
    fn a_shared_ref_map_links_separate_terms() {
        let prog = test_prog();
        let mut heap = QueryHeap::new(prog, None);
        let p = heap.symbols().set_const("p");
        let q = heap.symbols().set_const("q");

        let x = heap.new_var(super::VarReg::UNBOUND);
        heap.cells.extend([(Comp, 2), (Con, p), (Var, x)]); // p(X) at 0
        heap.cells.extend([(Comp, 2), (Con, q), (Var, x)]); // q(X) at 3

        let mut ref_map = HashMap::new();
        let first = heap.heap_len();
        heap.dup_term(0, &mut ref_map);
        let second = heap.heap_len();
        heap.dup_term(3, &mut ref_map);

        assert_eq!(
            heap[first + 2],
            heap[second + 2],
            "X in p(X) and X in q(X) must copy to the same variable"
        );
    }
}

#[cfg(test)]
mod check_constraints_tests {
    use super::super::{
        test_prog, Heap, QueryHeap,
        Tag::*,
        VarBind::{Addr, VarId},
        VarReg,
    };

    /// A heap with `n` unbound variable registers and nothing else.
    fn heap_with_vars(n: usize) -> QueryHeap<'static> {
        let mut heap = QueryHeap::new(test_prog(), None);
        for _ in 0..n {
            heap.new_var(VarReg::UNBOUND);
        }
        heap
    }

    #[test]
    fn distinct_unbound_variables_pass() {
        let heap = heap_with_vars(3);
        assert!(heap.check_constraints(&[0, 1, 2]));
    }

    /// Two members aliased onto one representative are the same variable, so
    /// the set must fail. This is the arm that catches an invented predicate
    /// being unified with the target.
    #[test]
    fn two_members_aliased_to_one_representative_fail() {
        let mut heap = heap_with_vars(3);
        heap.bind(1, VarId(0));
        assert!(
            !heap.check_constraints(&[0, 1]),
            "var 1 derefs to var 0, so the two are one variable"
        );
        assert!(
            !heap.check_constraints(&[1, 2, 0]),
            "position in the set must not matter"
        );
    }

    /// An alias chain longer than one hop still collapses.
    #[test]
    fn an_alias_chain_collapses() {
        let mut heap = heap_with_vars(3);
        heap.bind(2, VarId(1));
        heap.bind(1, VarId(0));
        assert!(!heap.check_constraints(&[0, 2]));
    }

    #[test]
    fn members_bound_to_distinct_constants_pass() {
        let mut heap = heap_with_vars(2);
        let a = heap.symbols().set_const("a");
        let b = heap.symbols().set_const("b");
        let addr_a = heap.heap_push((Con, a));
        let addr_b = heap.heap_push((Con, b));
        heap.bind(0, Addr(addr_a));
        heap.bind(1, Addr(addr_b));
        assert!(heap.check_constraints(&[0, 1]));
    }

    /// Distinct addresses holding structurally equal terms still clash --
    /// the `term_equal` arm. Comparing addresses alone would pass this.
    #[test]
    fn structurally_equal_terms_at_different_addresses_fail() {
        let mut heap = heap_with_vars(2);
        let p = heap.symbols().set_const("p");
        let a = heap.symbols().set_const("a");
        let first = heap.heap_push((Comp, 2));
        heap.heap_push((Con, p));
        heap.heap_push((Con, a));
        let second = heap.heap_push((Comp, 2));
        heap.heap_push((Con, p));
        heap.heap_push((Con, a));
        assert_ne!(first, second, "the fixture must use two distinct addresses");

        heap.bind(0, Addr(first));
        heap.bind(1, Addr(second));
        assert!(
            !heap.check_constraints(&[0, 1]),
            "p(a) and p(a) are the same term however many copies are on the heap"
        );
    }

    /// One member bound and one not can never clash: an unbound variable
    /// derefs to a `VarId`, a bound one to an `Addr`.
    #[test]
    fn a_bound_and_an_unbound_member_pass() {
        let mut heap = heap_with_vars(2);
        let a = heap.symbols().set_const("a");
        let addr = heap.heap_push((Con, a));
        heap.bind(0, Addr(addr));
        assert!(heap.check_constraints(&[0, 1]));
    }

    /// Degenerate sets hold vacuously -- there is no pair to violate.
    #[test]
    fn empty_and_singleton_sets_pass() {
        let heap = heap_with_vars(1);
        assert!(heap.check_constraints(&[]));
        assert!(heap.check_constraints(&[0]));
    }

    /// Beyond the `SmallVec` inline capacity of 8 the deref list spills to
    /// the heap; the answer must not change.
    #[test]
    fn a_set_wider_than_the_inline_capacity_is_still_correct() {
        let mut heap = heap_with_vars(12);
        let wide: Vec<usize> = (0..12).collect();
        assert!(
            heap.check_constraints(&wide),
            "twelve distinct unbound variables satisfy mutual inequality"
        );

        heap.bind(11, VarId(0));
        assert!(
            !heap.check_constraints(&wide),
            "a clash between the first and last members must be found past the spill"
        );
    }
}
