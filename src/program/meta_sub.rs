use smallvec::SmallVec;

use crate::{
    heap::{
        ArgRegs, Heap, QueryHeap,
        VarBind::{Addr, VarId},
        VarReg,
    },
    program::{
        PredicateTable, Clause,
    },
    resolution::{build, Substitution},
    META_SUBS_DEFAULT_SIZE,
};

#[derive(Debug, Clone)]
pub struct MetaSub {
    /// Where the meta clause sits in the predicate table's clause arena.
    /// Only good while that table is unchanged; see
    /// [`MetaSubTrait::template`].
    pub clause_idx: usize,
    /// Inline: one `MetaSub` is recorded for every clause the search adds to
    /// a hypothesis, so a `Vec` here cost an allocation per candidate clause
    /// to hold a handful of registers.
    pub subs: SmallVec<[VarReg; META_SUBS_DEFAULT_SIZE]>,
}

impl MetaSub {
    /// Read a meta clause's meta-variable bindings back out of the argument
    /// registers, after unifying its head against a goal.
    ///
    /// The meta variables are the contiguous run `threshold..max_arg_id`, so
    /// this is a slice copy rather than a filter over a bit set.
    pub fn from_arg_regs(
        arg_regs: &ArgRegs,
        clause_idx: usize,
        threshold: usize,
        max_arg_id: usize,
    ) -> Self {
        debug_assert!(
            max_arg_id <= arg_regs.len(),
            "a clause with {max_arg_id} variables cannot be read out of {} argument registers",
            arg_regs.len(),
        );
        Self {
            clause_idx,
            subs: SmallVec::from_slice(&arg_regs[threshold..max_arg_id]),
        }
    }

    /// Shift any subs that are addresses by step
    pub fn shift_addrs(&mut self, step: isize) {
        for sub in &mut self.subs {
            if sub.addr() {
                sub.0 = ((sub.0 as isize) + step).try_into().unwrap();
            }
        }
    }
}

/// A clause as the arena index of a meta clause and the bindings of its
/// meta variables.
///
/// Implemented by the owned [`MetaSub`] and by a packed `[usize]` holding
/// `[clause_idx, subs...]`, so a stored clause is read in place.
pub(crate) trait MetaSubTrait {
    fn clause_idx(&self) -> usize;

    fn subs(&self) -> impl ExactSizeIterator<Item = VarReg> + '_;

    /// The meta clause this substitution was taken against, read from its
    /// position in `predicate_table`'s clause arena.
    ///
    /// Only right while the table is as it was when the index was recorded:
    /// adding or removing clauses moves the arena. Nothing here can prove
    /// that, so a debug build checks what it can -- that the clause is a
    /// meta clause with as many meta variables as there are substitutions --
    /// which catches most stale indices without storing anything extra.
    fn template<'t>(&self, predicate_table: &'t PredicateTable) -> &'t Clause {
        let clause = predicate_table
            .clause_at(self.clause_idx())
            .expect("a MetaSub's clause index is inside the clause arena");
        debug_assert!(
            clause
                .meta_threshold()
                .is_some_and(|threshold| clause.max_arg_id - threshold == self.subs().len()),
            "the clause at arena index {} is not a meta clause with {} meta variables: \
             the predicate table was changed while this MetaSub was held",
            self.clause_idx(),
            self.subs().len(),
        );
        clause
    }

    /// Build the first-order clause this substitution stands for.
    fn build_clause(&self, heap: &mut impl Heap, predicate_table: &PredicateTable) -> Clause {
        self.build_clause_from_meta(heap, self.template(predicate_table))
    }

    /// As [`Self::build_clause`], with the meta clause template supplied
    /// directly.
    ///
    /// Mirrors the clause construction in
    /// `Env::try_choices`, with the substitution
    /// read back out of `self` instead of the live argument registers. The
    /// meta variables' bindings are inlined as terms; every other variable
    /// stays an `Arg` cell, leaving a template a later proof can instantiate.
    /// That is what passing the meta-variable flags to [`build`] buys -- it is
    /// not cosmetic, since without them an unbound `Arg` falls through to
    /// `Heap::set_var`, which the program heap refuses.
    fn build_clause_from_meta(&self, heap: &mut impl Heap, meta_clause: &Clause) -> Clause {
        let threshold = meta_clause
            .meta_threshold()
            .expect("a MetaSub's clause is always a meta clause");

        let mut substitution = Substitution::new(meta_clause.max_arg_id);
        for (arg_id, sub) in (threshold..meta_clause.max_arg_id).zip(self.subs()) {
            let binding = sub
                .get_bind()
                .expect("MetaSub subs are always populated from bound arg registers");
            debug_assert!(
                matches!(binding, Addr(_)),
                "meta var {arg_id} of meta clause {} is still a variable;                  building it would write a dangling Ref into the program heap",
                self.clause_idx()
            );
            substitution.set_arg(arg_id, binding);
        }

        let literals: Vec<usize> = meta_clause
            .iter()
            .map(|&literal| build(heap, &mut substitution, Some(threshold), literal))
            .collect();

        Clause::new(literals, None, meta_clause.max_arg_id)
    }

    /// Unify the two substitutions position by position, returning the
    /// variables bound, or `None` (with nothing left bound) if they differ.
    fn unify<O: MetaSubTrait + ?Sized>(
        &self,
        other: &O,
        heap: &mut QueryHeap,
    ) -> Option<Vec<usize>> {
        let mut binding = Vec::with_capacity(self.subs().len());
        for (msub1, msub2) in self.subs().zip(other.subs()) {
            if msub1 == msub2 {
                continue;
            }
            let b1 = if msub1.var() {
                heap.var_deref(msub1.value())
            } else {
                Addr(msub1.value())
            };
            let b2 = if msub2.var() {
                heap.var_deref(msub2.value())
            } else {
                Addr(msub2.value())
            };
            // Two different registers can still resolve to the same thing --
            // typically because an earlier position in this very loop aliased
            // one to the other. Binding then would make a variable point at
            // itself, and `var_deref` follows variable links until it reaches
            // something that is not one, so the next dereference would spin
            // forever.
            if b1 == b2 {
                continue;
            }
            match (b1, b2) {
                (VarId(var_id), other) | (other, VarId(var_id)) => {
                    binding.push(var_id);
                    heap.bind(var_id, other);
                }
                (Addr(addr1), Addr(addr2)) => {
                    if !heap.term_equal(addr1, addr2) {
                        heap.unbind(&binding);
                        return None;
                    }
                }
            }
        }
        Some(binding)
    }
}

impl MetaSubTrait for MetaSub {
    fn clause_idx(&self) -> usize {
        self.clause_idx
    }

    fn subs(&self) -> impl ExactSizeIterator<Item = VarReg> + '_ {
        self.subs.iter().copied()
    }
}

impl MetaSubTrait for [usize] {
    fn clause_idx(&self) -> usize {
        self[0]
    }

    fn subs(&self) -> impl ExactSizeIterator<Item = VarReg> + '_ {
        self[1..].iter().map(|&word| VarReg(word))
    }
}

/// Groups of clauses packed back to back, each clause stored as
/// `[clause_idx, subs...]`.
///
/// A group is whatever the owner makes it: a predicate definition, a
/// hypothesis. Append-only.
#[derive(Debug, Default)]
pub(crate) struct PackedMetaSubs {
    words: Vec<usize>,
    /// End of each clause in `words`.
    clause_ends: Vec<u32>,
    /// End of each group in `clause_ends`.
    group_ends: Vec<u32>,
}

impl PackedMetaSubs {
    /// Append `group` as one group.
    pub(crate) fn push<'a, T: MetaSubTrait + ?Sized + 'a>(
        &mut self,
        group: impl IntoIterator<Item = &'a T>,
    ) {
        for meta_sub in group {
            let subs = meta_sub.subs();
            reserve_slowly(&mut self.words, 1 + subs.len());
            self.words.push(meta_sub.clause_idx());
            self.words.extend(subs.map(|sub| sub.0));
            reserve_slowly(&mut self.clause_ends, 1);
            self.clause_ends
                .push(u32::try_from(self.words.len()).expect("more than u32::MAX packed words"));
        }
        reserve_slowly(&mut self.group_ends, 1);
        self.group_ends.push(
            u32::try_from(self.clause_ends.len()).expect("more than u32::MAX packed clauses"),
        );
    }

    /// Number of groups.
    pub(crate) fn len(&self) -> usize {
        self.group_ends.len()
    }

    pub(crate) fn get(&self, index: usize) -> MetaSubGroup<'_> {
        let first = match index {
            0 => 0,
            _ => self.group_ends[index - 1] as usize,
        };
        let start = match first {
            0 => 0,
            _ => self.clause_ends[first - 1] as usize,
        };
        MetaSubGroup {
            words: &self.words,
            ends: &self.clause_ends[first..self.group_ends[index] as usize],
            start,
        }
    }

    pub(crate) fn iter(&self) -> impl ExactSizeIterator<Item = MetaSubGroup<'_>> {
        (0..self.len()).map(|index| self.get(index))
    }
}

/// Make room for `additional` more elements. A `Vec` doubles when full,
/// leaving up to half of a large one unused; past [`DOUBLE_BELOW`] elements
/// this grows it by an eighth.
fn reserve_slowly<T>(vec: &mut Vec<T>, additional: usize) {
    /// Capacity up to which a `Vec` is left to double.
    const DOUBLE_BELOW: usize = 1 << 20;

    if vec.capacity() - vec.len() >= additional {
        return;
    }
    if vec.capacity() < DOUBLE_BELOW {
        vec.reserve(additional);
    } else {
        vec.reserve_exact(additional.max(vec.capacity() / 8));
    }
}

/// One group of a [`PackedMetaSubs`], read in place.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MetaSubGroup<'a> {
    words: &'a [usize],
    /// End of each of this group's clauses in `words`.
    ends: &'a [u32],
    /// Start of the first clause in `words`.
    start: usize,
}

impl<'a> MetaSubGroup<'a> {
    /// Number of clauses.
    pub(crate) fn len(&self) -> usize {
        self.ends.len()
    }

    pub(crate) fn get(&self, index: usize) -> &'a [usize] {
        let start = match index {
            0 => self.start,
            _ => self.ends[index - 1] as usize,
        };
        &self.words[start..self.ends[index] as usize]
    }

    pub(crate) fn iter(&self) -> impl ExactSizeIterator<Item = &'a [usize]> + '_ {
        (0..self.len()).map(|index| self.get(index))
    }
}

#[cfg(test)]
mod packed_tests {
    use super::{MetaSub, MetaSubTrait, PackedMetaSubs};
    use crate::heap::VarReg;

    fn meta_sub(clause_idx: usize, subs: &[usize]) -> MetaSub {
        MetaSub {
            clause_idx,
            subs: subs.iter().map(|&addr| VarReg::from_addr(addr)).collect(),
        }
    }

    #[test]
    fn groups_read_back_as_pushed() {
        let groups = vec![
            vec![meta_sub(3, &[10, 11, 12]), meta_sub(4, &[13])],
            vec![],
            vec![meta_sub(5, &[]), meta_sub(6, &[14, 15]), meta_sub(7, &[16, 17, 18, 19])],
        ];
        let mut packed = PackedMetaSubs::default();
        for group in &groups {
            packed.push(group);
        }

        assert_eq!(packed.len(), groups.len());
        for (stored, group) in packed.iter().zip(&groups) {
            assert_eq!(stored.len(), group.len());
            for (clause, meta_sub) in stored.iter().zip(group) {
                assert_eq!(clause.clause_idx(), meta_sub.clause_idx);
                assert!(clause.subs().eq(meta_sub.subs()));
            }
        }
    }

    #[test]
    fn a_large_vec_grows_by_an_eighth() {
        let mut small: Vec<u32> = Vec::with_capacity(4);
        small.extend([0; 4]);
        super::reserve_slowly(&mut small, 1);
        assert!(small.capacity() >= 8, "a small Vec still doubles");

        let mut large: Vec<u32> = Vec::with_capacity(1 << 20);
        large.resize(1 << 20, 0);
        super::reserve_slowly(&mut large, 1);
        assert_eq!(large.capacity(), (1 << 20) + (1 << 17));

        // Room already there: nothing changes.
        super::reserve_slowly(&mut large, 1);
        assert_eq!(large.capacity(), (1 << 20) + (1 << 17));
    }

    #[test]
    fn a_packed_clause_can_be_pushed_again() {
        let mut first = PackedMetaSubs::default();
        first.push(&[meta_sub(3, &[10, 11])]);
        let mut second = PackedMetaSubs::default();
        second.push(first.get(0).iter());

        assert_eq!(second.get(0).get(0), first.get(0).get(0));
    }
}

#[cfg(test)]
mod build_clause_tests {
    

    use super::{MetaSub, MetaSubTrait};
    use crate::{
        heap::{Cell, Heap, ProgramHeap, Tag::*, VarReg},
        parser::_build_clause,
        program::{Clause, PredicateTable},
    };

    // These tests assert on cells rather than `Clause::to_string`. An `Arg`
    // cell is named through `get_var(addr, heap_id)`, keyed on the cell's
    // *address*, and a program heap always reports heap_id 0 -- so two tests
    // sharing a program heap would write names to the same keys and read back
    // each other's. Each test here builds its own `ProgramHeap`, which now
    // carries its own table, so that no longer bites; cells remain the sharper
    // assertion either way, since the distinction this code turns on is `Arg`
    // vs `Ref` and a rendered string hides it.

    /// A program heap holding one meta clause template, plus the constants
    /// named in `consts` pushed after it.
    fn prog_with_meta<const N: usize>(
        meta_src: &str,
        consts: [&'static str; N],
    ) -> (ProgramHeap, Clause, [usize; N]) {
        let mut prog_heap = ProgramHeap::new();
        let meta = _build_clause(&mut prog_heap, meta_src);
        let addrs = consts.map(|name| {
            let symbol = prog_heap.symbols().set_const(name);
            prog_heap.heap_push((Con, symbol))
        });
        (prog_heap, meta, addrs)
    }

    fn meta_sub_of(meta: &Clause, addrs: &[usize]) -> MetaSub {
        MetaSub {
            clause_idx: meta.meta_data.unwrap().id,
            subs: addrs.iter().map(|&addr| VarReg::from_addr(addr)).collect(),
        }
    }

    /// The functor cell followed by one cell per argument.
    fn literal_cells(heap: &ProgramHeap, addr: usize) -> Vec<Cell> {
        heap.str_args(addr)
            .into_iter()
            .map(|arg_addr| heap[arg_addr])
            .collect()
    }

    /// A `Con` cell naming `name` in `prog`'s table.
    ///
    /// Takes the heap because the fixtures below build their own: an id
    /// interned anywhere else would not denote the same symbol in the heap
    /// under test.
    fn con(prog: &ProgramHeap, name: &str) -> Cell {
        (Con, prog.symbols().set_const(name))
    }

    #[test]
    fn every_meta_var_substituted() {
        // p(X,Y):-q(X),r(Y).
        let (mut prog_heap, meta, [p, q, r]) =
            prog_with_meta("P(X,Y):-Q(X),R(Y),{P,Q,R}.", ["p", "q", "r"]);
        let meta_sub = meta_sub_of(&meta, &[p, q, r]);

        let clause = meta_sub.build_clause_from_meta(&mut prog_heap, &meta);

        assert_eq!(clause.len(), 3);
        assert_eq!(
            literal_cells(&prog_heap, clause.head()),
            vec![con(&prog_heap, "p"), (Arg, 0), (Arg, 1)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[0]),
            vec![con(&prog_heap, "q"), (Arg, 0)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[1]),
            vec![con(&prog_heap, "r"), (Arg, 1)]
        );
        assert!(
            !clause.meta(),
            "the built clause is first-order; its meta vars are now ground"
        );
        assert_eq!(clause.max_arg_id, meta.max_arg_id);
    }

    #[test]
    fn first_order_args_stay_arg_cells() {
        // The built clause is a template a later proof instantiates, so every
        // position that was not a meta variable must survive as an `Arg` cell
        // carrying its original arg id -- not a fresh `Ref`, which on the
        // program heap would dangle into a dead query heap.
        let (mut prog_heap, meta, [p, q, r]) =
            prog_with_meta("P(X,Y):-Q(X),R(Y),{P,Q,R}.", ["p", "q", "r"]);
        let meta_sub = meta_sub_of(&meta, &[p, q, r]);

        let clause = meta_sub.build_clause_from_meta(&mut prog_heap, &meta);

        let head_args = literal_cells(&prog_heap, clause.head());
        assert_eq!(
            &head_args[1..],
            &[(Arg, 0), (Arg, 1)],
            "X and Y keep the arg ids they had in the template"
        );
        assert!(
            prog_heap.iter().all(|cell| cell.0 != Var),
            "no Ref cell may reach the program heap"
        );
    }

    #[test]
    fn substitutes_only_the_flagged_positions() {
        // A meta clause whose head predicate is a meta variable but whose body
        // predicate is already a constant: only the head functor is replaced,
        // and the body is copied through untouched.
        let (mut prog_heap, meta, [p]) = prog_with_meta("P(X,Y):-q(X,Y),{P}.", ["p"]);
        let meta_sub = meta_sub_of(&meta, &[p]);

        let clause = meta_sub.build_clause_from_meta(&mut prog_heap, &meta);

        assert_eq!(
            literal_cells(&prog_heap, clause.head()),
            vec![con(&prog_heap, "p"), (Arg, 0), (Arg, 1)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[0]),
            vec![con(&prog_heap, "q"), (Arg, 0), (Arg, 1)]
        );
    }

    #[test]
    fn looked_up_through_the_predicate_table() {
        let (mut prog_heap, meta, [p, q, r]) =
            prog_with_meta("P(X,Y):-Q(X),R(Y),{P,Q,R}.", ["p", "q", "r"]);
        let meta_id = meta.meta_data.unwrap().id;

        let mut predicate_table = PredicateTable::new();
        let symbol_arity = prog_heap.symbol_arity(meta.head());
        predicate_table
            .add_clause_to_predicate(meta.clone(), symbol_arity)
            .unwrap();
        let stored = predicate_table.get_meta_clause(meta_id).unwrap();
        let meta_sub = MetaSub {
            clause_idx: predicate_table.index_of(stored).unwrap(),
            subs: [p, q, r].map(VarReg::from_addr).into_iter().collect(),
        };

        let clause = meta_sub.build_clause(&mut prog_heap, &predicate_table);
        assert_eq!(
            literal_cells(&prog_heap, clause.head()),
            vec![con(&prog_heap, "p"), (Arg, 0), (Arg, 1)]
        );
    }

    /// A table holding the meta clause `P(X,Y):-Q(X,Y)` under `(0, 2)`, and
    /// a `MetaSub` recorded against it.
    fn table_and_recorded_meta_sub(prog_heap: &mut ProgramHeap) -> (PredicateTable, Clause, MetaSub) {
        let meta = _build_clause(prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let mut predicate_table = PredicateTable::new();
        predicate_table
            .add_clause_to_predicate(meta.clone(), (0, 2))
            .unwrap();
        let stored = predicate_table
            .get_meta_clause(meta.meta_data.unwrap().id)
            .unwrap();
        let p = prog_heap.symbols().set_const("p");
        let p = prog_heap.heap_push((Con, p));
        let meta_sub = MetaSub {
            clause_idx: predicate_table.index_of(stored).unwrap(),
            subs: [p, p].map(VarReg::from_addr).into_iter().collect(),
        };
        (predicate_table, meta, meta_sub)
    }

    #[test]
    fn template_reads_the_meta_clause_by_arena_index() {
        let mut prog_heap = ProgramHeap::new();
        let (predicate_table, meta, meta_sub) = table_and_recorded_meta_sub(&mut prog_heap);

        assert_eq!(meta_sub.template(&predicate_table), &meta);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "the predicate table was changed while this MetaSub was held")]
    fn template_refuses_an_index_that_no_longer_holds_its_meta_clause() {
        let mut prog_heap = ProgramHeap::new();
        let (mut predicate_table, _meta, meta_sub) = table_and_recorded_meta_sub(&mut prog_heap);

        // (0, 1) sorts before (0, 2), so this moves the meta clause along.
        let fact = _build_clause(&mut prog_heap, "a(X).");
        predicate_table
            .add_clause_to_predicate(fact, (0, 1))
            .unwrap();

        meta_sub.template(&predicate_table);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "the predicate table was changed while this MetaSub was held")]
    fn template_refuses_a_meta_clause_with_a_different_number_of_meta_variables() {
        let mut prog_heap = ProgramHeap::new();
        let (mut predicate_table, _meta, meta_sub) = table_and_recorded_meta_sub(&mut prog_heap);

        // Put a three-variable meta clause where the two-variable one was.
        predicate_table.remove_predicate((0, 2));
        let wider = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        predicate_table
            .add_clause_to_predicate(wider, (0, 2))
            .unwrap();

        meta_sub.template(&predicate_table);
    }

    #[test]
    fn index_survives_entries_being_inserted_before_it() {
        // `predicates` is sorted, so adding a predicate that sorts earlier
        // shifts every entry index after it. The index is keyed on
        // symbol_arity precisely so that this does not disturb it.
        let mut prog_heap = ProgramHeap::new();
        let first = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let second = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}.");
        let (first_id, second_id) = (first.meta_data.unwrap().id, second.meta_data.unwrap().id);

        let mut predicate_table = PredicateTable::new();
        // Both are variable-headed, so both land under (0, 2), the second
        // appended after the first.
        predicate_table
            .add_clause_to_predicate(first.clone(), (0, 2))
            .unwrap();
        predicate_table
            .add_clause_to_predicate(second.clone(), (0, 2))
            .unwrap();

        // (0, 1) sorts before (0, 2) and so shifts that entry along.
        let fact = _build_clause(&mut prog_heap, "a(X).");
        predicate_table
            .add_clause_to_predicate(fact, (0, 1))
            .unwrap();

        assert_eq!(predicate_table.get_meta_clause(first_id), Some(&first));
        assert_eq!(predicate_table.get_meta_clause(second_id), Some(&second));
    }
}

#[cfg(test)]
mod tests {
    use crate::heap::test_prog;

    use super::{MetaSub, MetaSubTrait};
    use crate::heap::ProgramHeap;
    use crate::heap::{
        Heap, QueryHeap,
        Tag::Con,
        VarBind::{Addr, VarId},
        VarReg,
    };

    fn make_addr(heap: &mut QueryHeap, name: &str) -> usize {
        let prog = test_prog();
        let sym = prog.symbols().set_const(name);
        heap.heap_push((Con, sym))
    }

    fn fresh_meta_sub(clause_idx: usize, subs: Vec<VarReg>) -> MetaSub {
        MetaSub {
            clause_idx,
            subs: super::SmallVec::from_vec(subs),
        }
    }

    #[test]
    fn meta_sub_unification() {
        let prog_heap = ProgramHeap::new();

        // lhs all addr, rhs all var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);

            let lhs = fresh_meta_sub(
                0,
                vec![VarReg::from_addr(addr_p), VarReg::from_addr(addr_q)],
            );
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x), VarReg::from_var(var_y)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("lhs addrs should unify with rhs unbound vars");
            assert_eq!(binding, vec![var_x, var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
            assert_eq!(heap.var_deref(var_y), Addr(addr_q));
        }

        // lhs all var, rhs all addr
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x), VarReg::from_var(var_y)]);
            let rhs = fresh_meta_sub(
                0,
                vec![VarReg::from_addr(addr_p), VarReg::from_addr(addr_q)],
            );

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("lhs unbound vars should unify with rhs addrs");
            assert_eq!(binding, vec![var_x, var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
            assert_eq!(heap.var_deref(var_y), Addr(addr_q));
        }

        // lhs mixed, rhs mixed (also covers the already-equal shared-var fast path)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            let shared = heap.new_var(VarReg::UNBOUND);

            // position 0: lhs addr <-> rhs unbound var
            // position 1: lhs unbound var <-> rhs addr
            // position 2: lhs/rhs share the same unbound var (already equal, no binding needed)
            let lhs = fresh_meta_sub(
                0,
                vec![
                    VarReg::from_addr(addr_p),
                    VarReg::from_var(var_x),
                    VarReg::from_var(shared),
                ],
            );
            let rhs = fresh_meta_sub(
                0,
                vec![
                    VarReg::from_var(var_y),
                    VarReg::from_addr(addr_q),
                    VarReg::from_var(shared),
                ],
            );

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("mixed addr/var positions should unify");
            assert_eq!(binding, vec![var_y, var_x]);
            assert_eq!(heap.var_deref(var_y), Addr(addr_p));
            assert_eq!(heap.var_deref(var_x), Addr(addr_q));
            // Shared var was already equal on both sides, so it's left untouched
            assert_eq!(heap.var_deref(shared), VarId(shared));
        }
    }

    /// Two positions naming the same variable on each side.
    ///
    /// Position 0 aliases the two variables together, so at position 1 both
    /// registers resolve to the same variable. Binding it to itself would
    /// make `var_deref` -- which follows variable links until it reaches
    /// something that is not one -- loop forever on the next dereference, so
    /// this test hangs rather than fails if the guard is removed.
    #[test]
    fn repeated_variable_pair_does_not_self_bind() {
        let prog_heap = ProgramHeap::new();
        let mut heap = QueryHeap::new(&prog_heap, None);
        let var_a = heap.new_var(VarReg::UNBOUND);
        let var_b = heap.new_var(VarReg::UNBOUND);

        let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_a), VarReg::from_var(var_a)]);
        let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_b), VarReg::from_var(var_b)]);

        let binding = lhs
            .unify(&rhs, &mut heap)
            .expect("a variable repeated on both sides should unify with itself");

        assert_eq!(binding, vec![var_a], "only the first position binds");
        assert_eq!(heap.var_deref(var_a), VarId(var_b));
        assert_eq!(heap.var_deref(var_b), VarId(var_b));
    }

    /// The same shape, but the repeated variable meets an address the second
    /// time: the alias from position 0 must be followed to the live variable.
    #[test]
    fn repeated_variable_against_addr_follows_the_alias() {
        let prog_heap = ProgramHeap::new();
        let mut heap = QueryHeap::new(&prog_heap, None);
        let addr_p = make_addr(&mut heap, "p");
        let var_a = heap.new_var(VarReg::UNBOUND);
        let var_b = heap.new_var(VarReg::UNBOUND);

        let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_a), VarReg::from_var(var_a)]);
        let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_b), VarReg::from_addr(addr_p)]);

        let binding = lhs
            .unify(&rhs, &mut heap)
            .expect("the aliased variable should take the address");

        assert_eq!(binding, vec![var_a, var_b]);
        assert_eq!(heap.var_deref(var_a), Addr(addr_p));
        assert_eq!(heap.var_deref(var_b), Addr(addr_p));
    }

    #[test]
    fn meta_sub_unification_chain() {
        let prog_heap = ProgramHeap::new();

        // Var set to other var: match var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND); // chain target of var_x, still unbound
            let var_z = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, VarId(var_y)); // var_x -> var_y

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_z)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to another var should unify with a fresh var");
            // The end of the chain (var_y) is what gets bound, not var_x itself
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_x), VarId(var_z));
        }

        // Var set to other var: match addr
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, VarId(var_y)); // var_x -> var_y

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_addr(addr_p)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to another var should unify with an addr");
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
        }

        // Var set to addr: match var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p)); // var_x -> addr_p directly

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_y)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to an addr should unify with a fresh var");
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_y), Addr(addr_p));
        }

        // Var set to addr: match addr (equal addrs -> success, no new bindings)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p));

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_addr(addr_p)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to an addr should unify with the same addr");
            assert!(binding.is_empty());
        }

        // Var set to addr: match addr (different addrs -> failure, prior bindings unwound)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p));

            // position 0 binds var_y to addr_p, position 1 then fails on mismatched
            // addrs, so the position-0 binding should be unwound before returning None.
            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x), VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_y), VarReg::from_addr(addr_q)]);

            assert!(lhs.unify(&rhs, &mut heap).is_none());
            assert_eq!(heap.var_deref(var_y), VarId(var_y)); // binding was undone
        }
    }
}
