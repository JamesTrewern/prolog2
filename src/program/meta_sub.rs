use crate::{
    heap::{
        ArgRegs, Heap, QueryHeap,
        VarBind::{Addr, Var},
        VarReg,
    },
    program::{
        clause::{BitFlag64, Clause},
        predicate_table::PredicateTable,
    },
    resolution::{build, Substitution},
};

#[derive(Debug, Clone)]
pub struct MetaSub {
    pub meta_clause_id: usize,
    pub subs: Vec<VarReg>,
}

impl MetaSub {
    /// Build MetaSub from argument registers after unification and meta vars bitflags
    pub fn from_arg_regs(arg_regs: &ArgRegs, meta_clause_id: usize, meta_vars: BitFlag64) -> Self {
        let subs = arg_regs
            .into_iter()
            .enumerate()
            .filter_map(|(i, reg)| if meta_vars.get(i) { Some(*reg) } else { None })
            .collect();
        Self {
            meta_clause_id,
            subs,
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

    /// Build the first-order clause this substitution stands for.
    ///
    /// A `MetaSub` records only the id of the meta clause it was taken
    /// against and the bindings of that clause's meta variables, so the
    /// template is recovered from `predicate_table` by id. Returns `None` if
    /// the id names no clause in the table, which means the substitution has
    /// outlived its template.
    pub fn build_clause(
        &self,
        heap: &mut impl Heap,
        predicate_table: &PredicateTable,
    ) -> Option<Clause> {
        let meta_clause = predicate_table.get_meta_clause(self.meta_clause_id)?;
        Some(self.build_clause_from_meta(heap, meta_clause))
    }

    /// As [`Self::build_clause`], with the meta clause template supplied
    /// directly.
    ///
    /// Mirrors the clause construction in
    /// [`Env::try_choices`](crate::resolution::Env), with the substitution
    /// read back out of `self` instead of the live argument registers. The
    /// meta variables' bindings are inlined as terms; every other variable
    /// stays an `Arg` cell, leaving a template a later proof can instantiate.
    /// That is what passing the meta-variable flags to [`build`] buys -- it is
    /// not cosmetic, since without them an unbound `Arg` falls through to
    /// `Heap::set_var`, which the program heap refuses.
    pub fn build_clause_from_meta(&self, heap: &mut impl Heap, meta_clause: &Clause) -> Clause {
        let meta_vars = meta_clause
            .meta_vars()
            .expect("a MetaSub's clause is always a meta clause");

        let mut substitution = Substitution::new(meta_clause.max_arg_id);
        for (arg_id, sub) in meta_vars.iter().zip(self.subs.iter()) {
            let binding = sub
                .get_bind()
                .expect("MetaSub subs are always populated from bound arg registers");
            debug_assert!(
                matches!(binding, Addr(_)),
                "meta var {arg_id} of meta clause {} is still a variable;                  building it would write a dangling Ref into the program heap",
                self.meta_clause_id
            );
            substitution.set_arg(arg_id, binding);
        }

        let literals: Vec<usize> = meta_clause
            .iter()
            .map(|&literal| build(heap, &mut substitution, Some(meta_vars), literal))
            .collect();

        Clause::new(literals, None, meta_clause.max_arg_id)
    }

    pub fn unify(&self, other: &Self, heap: &mut QueryHeap) -> Option<Vec<usize>> {
        let mut binding = Vec::with_capacity(self.subs.len());
        for (msub1, msub2) in self.subs.iter().zip(other.subs.iter()) {
            if *msub1 == *msub2 {
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
            match (b1, b2) {
                (Var(var_id), other) | (other, Var(var_id)) => {
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

#[cfg(test)]
mod build_clause_tests {
    use super::MetaSub;
    use crate::{
        heap::{Cell, Heap, SymbolDB, Tag::*, VarReg},
        parser::_build_clause,
        program::{clause::Clause, predicate_table::PredicateTable},
    };

    // These tests assert on cells rather than `Clause::to_string`. An `Arg`
    // cell is named through `SymbolDB::get_var(addr, heap_id)`, a global map
    // keyed on the cell's *address*, and a `Vec<Cell>` program heap always
    // reports heap_id 0 -- so two tests parsing into their own program heap
    // write names to the same keys and read back each other's. Cells are also
    // the sharper assertion: the distinction this code turns on is `Arg` vs
    // `Ref`, which a rendered string hides.

    /// A program heap holding one meta clause template, plus the constants
    /// named in `consts` pushed after it.
    fn prog_with_meta<const N: usize>(
        meta_src: &str,
        consts: [&'static str; N],
    ) -> (Vec<Cell>, Clause, [usize; N]) {
        let mut prog_heap: Vec<Cell> = Vec::new();
        let meta = _build_clause(&mut prog_heap, meta_src);
        let addrs = consts.map(|name| {
            let symbol = SymbolDB::set_const(name);
            prog_heap.heap_push((Con, symbol))
        });
        (prog_heap, meta, addrs)
    }

    fn meta_sub_of(meta: &Clause, addrs: &[usize]) -> MetaSub {
        MetaSub {
            meta_clause_id: meta.meta_data.unwrap().id,
            subs: addrs.iter().map(|&addr| VarReg::from_addr(addr)).collect(),
        }
    }

    /// The functor cell followed by one cell per argument.
    fn literal_cells(heap: &Vec<Cell>, addr: usize) -> Vec<Cell> {
        heap.str_args(addr)
            .into_iter()
            .map(|arg_addr| heap[arg_addr])
            .collect()
    }

    fn con(name: &str) -> Cell {
        (Con, SymbolDB::set_const(name))
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
            vec![con("p"), (Arg, 0), (Arg, 1)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[0]),
            vec![con("q"), (Arg, 0)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[1]),
            vec![con("r"), (Arg, 1)]
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
            prog_heap.iter().all(|cell| cell.0 != Ref),
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
            vec![con("p"), (Arg, 0), (Arg, 1)]
        );
        assert_eq!(
            literal_cells(&prog_heap, clause.body()[0]),
            vec![con("q"), (Arg, 0), (Arg, 1)]
        );
    }

    #[test]
    fn looked_up_through_the_predicate_table() {
        let (mut prog_heap, meta, [p, q, r]) =
            prog_with_meta("P(X,Y):-Q(X),R(Y),{P,Q,R}.", ["p", "q", "r"]);
        let meta_sub = meta_sub_of(&meta, &[p, q, r]);
        let meta_id = meta.meta_data.unwrap().id;

        let mut predicate_table = PredicateTable::new();
        let symbol_arity = prog_heap.symbol_arity(meta.head());
        predicate_table
            .add_clause_to_predicate(meta.clone(), symbol_arity)
            .unwrap();

        assert_eq!(predicate_table.get_meta_clause(meta_id), Some(&meta));

        let clause = meta_sub
            .build_clause(&mut prog_heap, &predicate_table)
            .expect("the id was just added to the table");
        assert_eq!(
            literal_cells(&prog_heap, clause.head()),
            vec![con("p"), (Arg, 0), (Arg, 1)]
        );

        // An id the table never saw resolves to nothing rather than to some
        // other predicate's clause.
        assert!(predicate_table.get_meta_clause(meta_id + 10_000).is_none());
        assert!(
            meta_sub_of(&Clause::new(vec![], Some((vec![], vec![])), 0), &[])
                .build_clause(&mut prog_heap, &predicate_table)
                .is_none()
        );
    }

    #[test]
    fn index_survives_entries_being_inserted_before_it() {
        // `predicates` is sorted, so adding a predicate that sorts earlier
        // shifts every entry index after it. The index is keyed on
        // symbol_arity precisely so that this does not disturb it.
        let mut prog_heap: Vec<Cell> = Vec::new();
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
    use super::MetaSub;
    use crate::heap::{
        Cell, Heap, QueryHeap, SymbolDB,
        Tag::Con,
        VarBind::{Addr, Var},
        VarReg,
    };

    fn make_addr(heap: &mut QueryHeap, name: &str) -> usize {
        let sym = SymbolDB::set_const(name);
        heap.heap_push((Con, sym))
    }

    fn fresh_meta_sub(meta_clause_id: usize, subs: Vec<VarReg>) -> MetaSub {
        MetaSub {
            meta_clause_id,
            subs,
        }
    }

    #[test]
    fn meta_sub_unification() {
        let prog_heap: Vec<Cell> = vec![];

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
            assert_eq!(heap.var_deref(shared), Var(shared));
        }
    }

    #[test]
    fn meta_sub_unification_chain() {
        let prog_heap: Vec<Cell> = vec![];

        // Var set to other var: match var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND); // chain target of var_x, still unbound
            let var_z = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Var(var_y)); // var_x -> var_y

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_z)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to another var should unify with a fresh var");
            // The end of the chain (var_y) is what gets bound, not var_x itself
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_x), Var(var_z));
        }

        // Var set to other var: match addr
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Var(var_y)); // var_x -> var_y

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
            assert_eq!(heap.var_deref(var_y), Var(var_y)); // binding was undone
        }
    }
}
