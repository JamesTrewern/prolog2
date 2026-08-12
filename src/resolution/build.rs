//! Term building: construct new heap terms from clause templates and substitutions.

use crate::{
    heap::{Heap, QueryHeap, Tag::*, TermWalk, VarBind::*, Walk},
    program::clause::BitFlag64,
    resolution::Substitution,
};

/// If a ref if bound to some complex term which contains args we want
/// to rebuild this term in the query space replacing args with refs or arg reg values
pub fn re_build_bound_arg_terms(heap: &mut QueryHeap, substitution: &mut Substitution) {
    for i in 0..substitution.len() {
        if substitution.needs_rebuild[i] {
            // Assume if needs rebuild is true variable register is an addr
            let mut bound_addr = heap.var_regs[substitution[i]].value();
            //Update bound_addr to newly built term
            bound_addr = build(heap, substitution, None, bound_addr);
            // don't use heap.bind() to avoid overwrite guards
            heap.var_regs[substitution[i]] = Addr(bound_addr).into();
        }
    }
}

/// Build a new term from previous term and substitution.
/// Assume that src_addr does not point to bound ref.
pub fn build(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    let new_addr = heap.heap_len();
    let mut walk = TermWalk::new(src_addr);

    while let Some(cell) = walk.next_cell(heap) {
        if cell.0 == Arg {
            build_arg(heap, substitution, meta_vars, cell.1);
        } else {
            heap.heap_push(cell);
        }
    }
    new_addr
}

fn build_arg(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    arg_id: usize,
) {
    match meta_vars {
        Some(bit_flags) if !bit_flags.get(arg_id) => _ = heap.heap_push((Arg, arg_id)),
        _ => match substitution.get_arg(arg_id) {
            Some(Addr(bound_addr)) => _ = build(heap, substitution, meta_vars, bound_addr),
            Some(Var(var_id)) => _ = heap.heap_push((Ref, var_id)),
            None => {
                let var_id = heap.set_var(None);
                substitution.set_arg(arg_id, Var(var_id));
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{build, re_build_bound_arg_terms};
    use crate::{
        heap::{Cell, Heap, QueryHeap, SymbolDB, Tag::*, VarBind::*, VarReg, EMPTY_LIS, LIS},
        program::clause::{BitFlag64, MAX_ARG},
        resolution::{unify, Substitution},
    };

    //---------------------------------------------------------------------
    // Fixture conventions
    //---------------------------------------------------------------------
    //
    // Terms live in one of two places, and which one matters:
    //
    //   * The program heap (`QueryHeap::prog_cells`, an immutable `&[Cell]`)
    //     holds compiled clause templates. Their variables are `Arg` cells.
    //     `Ref` cells are query-time objects and never appear here.
    //
    //   * The query heap (`QueryHeap::cells`) holds goals and every term
    //     `build` produces. `Arg` cells appear here only inside hypothesis
    //     clause templates learned during the proof.
    //
    // Tests therefore put clause templates in the program heap and goals in
    // the query heap, matching what `env.rs` actually does. This is not just
    // realism: with an empty program heap the two address spaces both start at
    // zero and overlap exactly, so a bug that confuses a source address with a
    // destination address, or a term root with an arg id, can land on a
    // plausible-looking cell and pass. Keeping the regions disjoint turns those
    // into obviously wrong addresses.

    /// A cell no fixture ever legitimately produces.
    ///
    /// Every program fixture starts with one at address 0, so no real term
    /// begins at address 0. Code that falls back to address 0 by accident then
    /// shows up in an assertion instead of matching a real cell.
    fn poison() -> Cell {
        (Con, SymbolDB::set_const("__poison__"))
    }

    /// Build a program-heap fixture, checking the invariants above.
    fn prog(cells: Vec<Cell>) -> Vec<Cell> {
        assert_eq!(
            cells[0],
            poison(),
            "program fixture must begin with a poison cell"
        );
        assert!(
            !cells.iter().any(|c| c.0 == Ref),
            "program heap must not contain Ref cells; clause variables are Arg cells"
        );
        cells
    }

    //---------------------------------------------------------------------
    // re_build_bound_arg_terms: program space -> query space
    //---------------------------------------------------------------------
    //
    // `unify`'s `(Lis | Comp | Set | Tup, Ref)` arm binds the goal's `Ref` to
    // the *head* address. The head is a clause template, so that address is in
    // the program heap and the term behind it may contain `Arg` cells. `Arg`
    // ids are clause-local and the program heap is shared, so leaving a query
    // variable pointing there is not sound — `re_build_bound_arg_terms` copies
    // the term into query space with its args resolved.
    //
    // Rebuilding is therefore always a program-to-query copy, and every test
    // here is written that way.

    /// The minimal rebuild: one flagged binding onto a program term holding a
    /// single unbound `Arg`.
    #[test]
    fn rebuild_replaces_arg_with_fresh_ref() {
        let prog = prog(vec![
            poison(),  // 0
            LIS,       // 1: [A0]
            (Arg, 0),  // 2
            EMPTY_LIS, // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        // X (var 0) was left pointing at the program term at address 1.
        heap.var_regs = vec![Addr(1).into()];
        let mut sub = Substitution::default();
        sub.push_bound_var(0, true, Addr(1));

        re_build_bound_arg_terms(&mut heap, &mut sub);

        assert_eq!(heap[q..], [LIS, (Ref, 1), EMPTY_LIS]);
        assert_eq!(
            heap.var_regs[0],
            Addr(q).into(),
            "X must be repointed at the rebuilt copy in query space"
        );
        assert_eq!(
            heap.var_regs[1],
            VarReg::UNBOUND,
            "the variable invented for A0 starts unbound"
        );
        // Asserting the recording as well as the emitted cell: the cell alone
        // cannot tell us *which* arg the fresh variable was filed under.
        assert_eq!(
            sub.get_arg(0),
            Some(Var(1)),
            "the fresh variable must be recorded against arg 0"
        );
    }

    /// An unflagged binding points at a ground term, so there is nothing to
    /// copy. It must not allocate and must not be repointed.
    #[test]
    fn unflagged_binding_is_untouched() {
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 2), // 1: f(a)
            (Con, f),  // 2
            (Con, a),  // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);

        heap.var_regs = vec![Addr(1).into()];
        let mut sub = Substitution::default();
        sub.push_bound_var(0, false, Addr(1));

        let before = heap.heap_len();
        re_build_bound_arg_terms(&mut heap, &mut sub);

        assert_eq!(
            heap.heap_len(),
            before,
            "an unflagged binding must not allocate"
        );
        assert_eq!(
            heap.var_regs[0],
            Addr(1).into(),
            "an unflagged binding must not be repointed"
        );
    }

    /// Nested structure, two distinct args, and one arg used twice.
    ///
    /// The repeated `A0` must resolve to the same fresh variable in both
    /// positions, and `A0` and `A1` must stay distinct from each other. This
    /// also pins the postcondition the rest of the engine assumes:
    /// `Heap::normalise_args` states in a comment that "refs can't bind to arg
    /// terms without rebuilding" — after this call that must be true.
    #[test]
    fn rebuild_resolves_nested_args_and_preserves_sharing() {
        let p = SymbolDB::set_const("p");
        let g = SymbolDB::set_const("g");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 4), // 1: p(A0, g(A1, a), [A0])
            (Con, p),  // 2
            (Arg, 0),  // 3
            (Comp, 3), // 4:   g(A1, a)
            (Con, g),  // 5
            (Arg, 1),  // 6
            (Con, a),  // 7
            LIS,       // 8:   [A0]
            (Arg, 0),  // 9
            EMPTY_LIS, // 10
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.var_regs = vec![Addr(1).into()];
        let mut sub = Substitution::default();
        sub.push_bound_var(0, true, Addr(1));

        re_build_bound_arg_terms(&mut heap, &mut sub);

        assert_eq!(
            heap[q..],
            [
                (Comp, 4),
                (Con, p),
                (Ref, 1), // A0
                (Comp, 3),
                (Con, g),
                (Ref, 2), // A1 — must not collapse into A0
                (Con, a),
                LIS,
                (Ref, 1), // A0 again — must be the same variable
                EMPTY_LIS,
            ]
        );
        assert_eq!(sub.get_arg(0), Some(Var(1)));
        assert_eq!(sub.get_arg(1), Some(Var(2)));
        assert!(
            !heap.contains_args(q),
            "no Arg cells may survive a rebuild"
        );
        assert!(
            heap.var_regs[0].value() >= prog.len(),
            "the rebuilt term must live in query space, not the program heap"
        );
    }

    /// The fresh variables invented during a rebuild are recorded in the
    /// substitution, so body literals built afterwards reuse them rather than
    /// inventing their own. Without this, `p([A]) :- q(A)` would end up with
    /// two unrelated variables.
    #[test]
    fn rebuild_shares_fresh_var_with_later_goal_build() {
        let q_sym = SymbolDB::set_const("q");

        let prog = prog(vec![
            poison(),    // 0
            LIS,         // 1: head subterm [A0]
            (Arg, 0),    // 2
            EMPTY_LIS,   // 3
            (Comp, 2),   // 4: body literal q(A0)
            (Con, q_sym), // 5
            (Arg, 0),    // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.var_regs = vec![Addr(1).into()];
        let mut sub = Substitution::default();
        sub.push_bound_var(0, true, Addr(1));

        re_build_bound_arg_terms(&mut heap, &mut sub);
        let goal = build(&mut heap, &mut sub, None, 4);

        assert_eq!(
            heap[q..],
            [
                // rebuilt head subterm
                LIS,
                (Ref, 1),
                EMPTY_LIS,
                // body goal, reusing the same variable
                (Comp, 2),
                (Con, q_sym),
                (Ref, 1),
            ]
        );
        assert_eq!(goal, q + 3);
    }

    /// An arg that is already bound to a query-space term must be expanded
    /// inline, not turned into a fresh variable.
    ///
    /// This is also the arity check: `p/1` is `(Comp, 2)` — functor plus one
    /// subterm — and stays `(Comp, 2)` even though the substituted tuple
    /// occupies three cells, because the count is of subterms, not cells.
    #[test]
    fn rebuild_expands_arg_bound_to_query_term() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 2), // 1: p(A0)
            (Con, p),  // 2
            (Arg, 0),  // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        // The goal side already holds the tuple (a,b) in query space.
        heap.cells.extend([(Tup, 2), (Con, a), (Con, b)]); // q..q+3
        heap.var_regs = vec![Addr(1).into()];

        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(q));
        sub.push_bound_var(0, true, Addr(1));

        re_build_bound_arg_terms(&mut heap, &mut sub);

        assert_eq!(
            heap[q + 3..],
            [(Comp, 2), (Con, p), (Tup, 2), (Con, a), (Con, b)]
        );
        assert_eq!(heap.term_string(q + 3), "p((a,b))");
        assert_eq!(heap.var_regs[0], Addr(q + 3).into());
    }

    /// Two variables bound to the *same* program term are rebuilt
    /// independently, producing two separate copies.
    ///
    /// The copies share variables (both hold the same fresh `Ref`), so this is
    /// sound, but the storage is duplicated and the two registers point at
    /// different addresses. Recorded here so that if the loop ever grows a
    /// cache, the change is deliberate.
    #[test]
    fn two_vars_bound_to_same_term_get_separate_copies() {
        let prog = prog(vec![
            poison(),  // 0
            LIS,       // 1: [A0]
            (Arg, 0),  // 2
            EMPTY_LIS, // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.var_regs = vec![Addr(1).into(), Addr(1).into()];
        let mut sub = Substitution::default();
        sub.push_bound_var(0, true, Addr(1));
        sub.push_bound_var(1, true, Addr(1));

        re_build_bound_arg_terms(&mut heap, &mut sub);

        assert_eq!(
            heap[q..],
            [LIS, (Ref, 2), EMPTY_LIS, LIS, (Ref, 2), EMPTY_LIS],
            "each flagged binding gets its own copy, sharing the same variable"
        );
        assert_eq!(heap.var_regs[0], Addr(q).into());
        assert_eq!(heap.var_regs[1], Addr(q + 3).into());
        assert_ne!(
            heap.var_regs[0], heap.var_regs[1],
            "the two copies are distinct terms"
        );
    }

    //---------------------------------------------------------------------
    // build with meta_vars = None: clause body -> new goals
    //---------------------------------------------------------------------
    //
    // This is the `env.rs` path
    //   `clause.body().iter().map(|&l| build(heap, &mut substitution, None, l))`.
    // The body literal is a clause template in the program heap; the goal it
    // produces must be a self-contained query-space term with every `Arg`
    // resolved. The substitution is threaded by `&mut` across the whole body,
    // which is what makes a variable shared between two body literals the same
    // variable.

    /// Distinct arg ids must map to distinct variables, and a repeated arg id
    /// to the same variable.
    ///
    /// This is the sharpest test of arg identity in the suite: it is the one
    /// that fails if an arg id is ever sourced from anything other than the
    /// `Arg` cell itself.
    #[test]
    fn distinct_args_get_distinct_vars() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 4), // 1: p(A0, A0, A1)
            (Con, p),  // 2
            (Arg, 0),  // 3
            (Arg, 0),  // 4
            (Arg, 1),  // 5
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();
        let mut sub = Substitution::default();

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(goal, q);
        assert_eq!(
            heap[q..],
            [(Comp, 4), (Con, p), (Ref, 0), (Ref, 0), (Ref, 1)]
        );
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert_eq!(sub.get_arg(1), Some(Var(1)));
        assert_eq!(heap.var_regs, [VarReg::UNBOUND, VarReg::UNBOUND]);
        assert!(!heap.contains_args(goal));
    }

    /// An arg already bound to a variable emits that variable and must not
    /// allocate a new register.
    #[test]
    fn arg_bound_to_var_emits_ref_without_allocating() {
        let q_sym = SymbolDB::set_const("q");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: q(A0)
            (Con, q_sym), // 2
            (Arg, 0),     // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        // Three query variables already exist; arg 0 is bound to the last.
        heap.var_regs = vec![VarReg::UNBOUND; 3];
        let mut sub = Substitution::default();
        sub.set_arg(0, Var(2));

        build(&mut heap, &mut sub, None, 1);

        assert_eq!(heap[q..], [(Comp, 2), (Con, q_sym), (Ref, 2)]);
        assert_eq!(
            heap.var_regs.len(),
            3,
            "an already-bound arg must not invent a variable"
        );
    }

    /// An arg bound to a query-space address is expanded inline, and the
    /// expansion is a copy: mutating the source afterwards must not change it.
    #[test]
    fn arg_bound_to_addr_copies_structure() {
        let q_sym = SymbolDB::set_const("q");
        let f = SymbolDB::set_const("f");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: q(A0)
            (Con, q_sym), // 2
            (Arg, 0),     // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([(Comp, 2), (Con, f), (Con, a)]); // q..q+3: f(a)
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(q));

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(goal, q + 3);
        assert_eq!(heap.term_string(goal), "q(f(a))");
        let built = heap[goal..].to_vec();
        assert_eq!(built, [(Comp, 2), (Con, q_sym), (Comp, 2), (Con, f), (Con, a)]);

        // Perturb the source term; the built goal must be unaffected.
        heap.cells[2] = (Con, b);
        assert_eq!(heap[goal..], built[..], "the built goal must be a copy");
    }

    /// A substituted term may itself be a clause template containing further
    /// args, so expansion has to recurse.
    #[test]
    fn arg_bound_to_addr_containing_further_args() {
        let q_sym = SymbolDB::set_const("q");
        let g = SymbolDB::set_const("g");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: q(A0)
            (Con, q_sym), // 2
            (Arg, 0),     // 3
            (Comp, 2),    // 4: g(A1)
            (Con, g),     // 5
            (Arg, 1),     // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(4));

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(
            heap[q..],
            [(Comp, 2), (Con, q_sym), (Comp, 2), (Con, g), (Ref, 0)]
        );
        assert_eq!(sub.get_arg(1), Some(Var(0)));
        assert!(
            !heap.contains_args(goal),
            "recursion must resolve args at every depth"
        );
    }

    /// The variable a body literal invents for an arg must be reused by the
    /// next body literal. This is what makes `p(A) :- q(A), r(A)` work, and it
    /// is the reason `build` takes the substitution by `&mut`.
    #[test]
    fn fresh_vars_shared_across_body_literals() {
        let q_sym = SymbolDB::set_const("q");
        let r = SymbolDB::set_const("r");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: q(A0)
            (Con, q_sym), // 2
            (Arg, 0),     // 3
            (Comp, 2),    // 4: r(A0)
            (Con, r),     // 5
            (Arg, 0),     // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();
        let mut sub = Substitution::default();

        let g1 = build(&mut heap, &mut sub, None, 1);
        let g2 = build(&mut heap, &mut sub, None, 4);

        assert_eq!((g1, g2), (q, q + 3));
        assert_eq!(
            heap[q..],
            [
                (Comp, 2),
                (Con, q_sym),
                (Ref, 0),
                (Comp, 2),
                (Con, r),
                (Ref, 0),
            ]
        );
        assert_eq!(
            heap.var_regs.len(),
            1,
            "the two literals must share one variable, not invent two"
        );
    }

    /// Args are resolved under every structure tag, not just `Comp`.
    ///
    /// `handle_cell_increment` treats `Comp`, `Tup` and `Set` alike and gives
    /// `LIS` a fixed span of two, so this walks all four in one term.
    #[test]
    fn all_structure_tags_expand_args() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 4), // 1: p({A0,A1}, (A2,A3), [A4|A5])
            (Con, p),  // 2
            (Set, 2),  // 3
            (Arg, 0),  // 4
            (Arg, 1),  // 5
            (Tup, 2),  // 6
            (Arg, 2),  // 7
            (Arg, 3),  // 8
            LIS,       // 9
            (Arg, 4),  // 10
            (Arg, 5),  // 11
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();
        let mut sub = Substitution::default();

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(
            heap[q..],
            [
                (Comp, 4),
                (Con, p),
                (Set, 2),
                (Ref, 0),
                (Ref, 1),
                (Tup, 2),
                (Ref, 2),
                (Ref, 3),
                LIS,
                (Ref, 4),
                (Ref, 5),
            ]
        );
        assert!(!heap.contains_args(goal));
        assert_eq!(heap.var_regs.len(), 6, "six distinct args, six variables");
    }

    /// A list whose tail is an arg bound to another list must splice, not
    /// nest. The arity of the enclosing cells is unaffected because `LIS`
    /// always spans exactly two subterms.
    #[test]
    fn list_with_arg_tail_splices() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");

        let prog = prog(vec![
            poison(), // 0
            LIS,      // 1: [a,b|A0]
            (Con, a), // 2
            LIS,      // 3
            (Con, b), // 4
            (Arg, 0), // 5
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([LIS, (Con, c), EMPTY_LIS]); // q..q+3: [c]
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(q));

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(
            heap[goal..],
            [LIS, (Con, a), LIS, (Con, b), LIS, (Con, c), EMPTY_LIS]
        );
        assert_eq!(heap.term_string(goal), "[a,b,c]");
    }

    /// `EMPTY_LIS` must survive as `ELis`, not decay into some other zero-
    /// valued cell. `unify` has a history of conflating tags that share a
    /// value, and `(ELis, 0)` collides with `(Int, 0)`.
    #[test]
    fn arg_bound_to_empty_list() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 2), // 1: p(A0)
            (Con, p),  // 2
            (Arg, 0),  // 3
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([EMPTY_LIS]); // q
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(q));

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(heap[goal..], [(Comp, 2), (Con, p), EMPTY_LIS]);
        assert_eq!(heap[goal + 2].0, ELis);
    }

    /// A template with no args is copied verbatim. The control case: it must
    /// stay green under every mutation that only affects arg handling.
    #[test]
    fn ground_template_is_copied_verbatim() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: p(a, [a])
            (Con, p),  // 2
            (Con, a),  // 3
            LIS,       // 4
            (Con, a),  // 5
            EMPTY_LIS, // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();
        let mut sub = Substitution::default();

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(
            heap[q..],
            [(Comp, 3), (Con, p), (Con, a), LIS, (Con, a), EMPTY_LIS]
        );
        assert_eq!(goal, q);
        assert_eq!(
            heap.var_regs.len(),
            0,
            "a ground template invents no variables"
        );
        assert_eq!(sub.get_arg(0), None, "and records nothing");
    }

    /// A template that is a bare `Arg` — the single-cell edge case, where the
    /// only cell pushed comes from `set_var` rather than the copy path.
    #[test]
    fn bare_arg_template() {
        let prog = prog(vec![
            poison(), // 0
            (Arg, 0), // 1
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();
        let mut sub = Substitution::default();

        let goal = build(&mut heap, &mut sub, None, 1);

        assert_eq!(goal, q, "build returns the heap length captured before it pushes");
        assert_eq!(heap[q..], [(Ref, 0)]);
        assert_eq!(sub.get_arg(0), Some(Var(0)));
    }

    //---------------------------------------------------------------------
    // build with meta_vars = Some(..): metarule -> learned clause
    //---------------------------------------------------------------------
    //
    // A metarule such as `P(X,Y) :- Q(X,Y)` has two kinds of variable. The
    // second-order ones (`P`, `Q`) are flagged in `meta_vars` and must be
    // substituted, turning the schema into a concrete predicate. The ordinary
    // ones (`X`, `Y`) must survive as `Arg` cells, because the learned clause
    // is itself a template that will be matched against future goals.
    //
    // So unlike goal building, a *correct* result here still contains `Arg`
    // cells. The guard `Some(flags) if !flags.get(arg_id)` fires first and
    // short-circuits before the substitution is consulted at all.

    /// Flagged args are substituted; unflagged args are emitted verbatim.
    #[test]
    fn non_meta_args_pass_through_unchanged() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: A0(A1, A2) — the metarule head
            (Arg, 0),  // 2   A0 is the predicate symbol
            (Arg, 1),  // 3
            (Arg, 2),  // 4
            (Con, p),  // 5: the symbol A0 is bound to
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(5));

        let literal = build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(heap[q..], [(Comp, 3), (Con, p), (Arg, 1), (Arg, 2)]);
        assert!(
            heap.contains_args(literal),
            "a learned clause keeps its ordinary variables as Arg cells"
        );
        assert_eq!(
            (sub.get_arg(1), sub.get_arg(2)),
            (None, None),
            "unflagged args must not be recorded against the substitution"
        );
    }

    /// The unflagged guard is checked *before* the substitution, so an
    /// unflagged arg is emitted verbatim even when a binding for it exists.
    ///
    /// `env.rs` relies on this: it builds the body goals with `None` first,
    /// which populates the substitution for every arg, and only then builds
    /// the clause literals with `Some(..)`.
    #[test]
    fn non_meta_arg_ignores_an_existing_binding() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: A0(A1, A2)
            (Arg, 0),  // 2
            (Arg, 1),  // 3
            (Arg, 2),  // 4
            (Con, p),  // 5
            (Con, a),  // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(5));
        sub.set_arg(1, Addr(6)); // deliberately bound, but not a meta var
        sub.set_arg(2, Var(0));

        build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(
            heap[q..],
            [(Comp, 3), (Con, p), (Arg, 1), (Arg, 2)],
            "bindings for unflagged args must be ignored"
        );
    }

    /// A meta var with no binding falls through to the fresh-variable branch,
    /// leaving a free variable in predicate position.
    ///
    /// This is the state when predicate invention did not fire. Recorded to
    /// pin the current behaviour rather than to endorse it — `env.rs` still
    /// has a `todo!("push invented pred, could be ignored")` on that path.
    #[test]
    fn unbound_meta_var_creates_fresh_var() {
        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: A0(A1, A2)
            (Arg, 0),  // 2
            (Arg, 1),  // 3
            (Arg, 2),  // 4
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let mut sub = Substitution::default();

        build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(heap[q..], [(Comp, 3), (Ref, 0), (Arg, 1), (Arg, 2)]);
        assert_eq!(sub.get_arg(0), Some(Var(0)));
    }

    /// A meta var bound to a variable rather than an address emits that
    /// variable — the middle branch of `build_arg` under meta mode.
    #[test]
    fn meta_var_bound_to_var_emits_ref() {
        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: A0(A1, A2)
            (Arg, 0),  // 2
            (Arg, 1),  // 3
            (Arg, 2),  // 4
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.var_regs = vec![VarReg::UNBOUND; 2];
        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let mut sub = Substitution::default();
        sub.set_arg(0, Var(1));

        build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(heap[q..], [(Comp, 3), (Ref, 1), (Arg, 1), (Arg, 2)]);
        assert_eq!(heap.var_regs.len(), 2, "no variable should be invented");
    }

    /// The full `env.rs` sequence for a meta clause: body goals are built with
    /// `None`, then the clause literals with `Some(meta_vars)`.
    ///
    /// Metarule `P(X,Y) :- Q(X,Y)` with `P = p` and `Q = q` must yield the goal
    /// `q(_0, _1)` and the learned clause `p(A1,A2) :- q(A1,A2)`. The ordering
    /// matters: by the time the second loop runs, the substitution holds
    /// variables for `X` and `Y`, and the learned clause must still ignore them.
    #[test]
    fn metarule_end_to_end_matches_env_ordering() {
        let p = SymbolDB::set_const("p");
        let q_sym = SymbolDB::set_const("q");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 3),    // 1: head A0(A1, A2)
            (Arg, 0),     // 2
            (Arg, 1),     // 3
            (Arg, 2),     // 4
            (Comp, 3),    // 5: body A3(A1, A2)
            (Arg, 3),     // 6
            (Arg, 1),     // 7
            (Arg, 2),     // 8
            (Con, p),     // 9
            (Con, q_sym), // 10
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0); // P
        meta_vars.set(3); // Q
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(9));
        sub.set_arg(3, Addr(10));

        // env.rs: build the body goals first, with meta_vars = None.
        let goal = build(&mut heap, &mut sub, None, 5);
        // env.rs: then build the clause literals, with meta_vars = Some(..).
        let new_head = build(&mut heap, &mut sub, Some(meta_vars), 1);
        let new_body = build(&mut heap, &mut sub, Some(meta_vars), 5);

        assert_eq!((goal, new_head, new_body), (q, q + 4, q + 8));
        assert_eq!(
            heap[q..],
            [
                // goal: q(_0, _1)
                (Comp, 3),
                (Con, q_sym),
                (Ref, 0),
                (Ref, 1),
                // learned head: p(A1, A2)
                (Comp, 3),
                (Con, p),
                (Arg, 1),
                (Arg, 2),
                // learned body: q(A1, A2)
                (Comp, 3),
                (Con, q_sym),
                (Arg, 1),
                (Arg, 2),
            ]
        );
        assert!(
            !heap.contains_args(goal),
            "the goal is resolved and must hold no args"
        );
        assert!(
            heap.contains_args(new_head) && heap.contains_args(new_body),
            "the learned clause is a template and must keep its args"
        );
    }

    /// The top of the arg range. `MAX_ARG` is 64 and `BitFlag64` covers
    /// indices 0..=63, so both the flagged and unflagged paths must work at
    /// the boundary rather than overflowing the shift or the register array.
    #[test]
    fn meta_flags_work_at_the_top_of_the_arg_range() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: A63(A62, A0)
            (Arg, 63), // 2  flagged
            (Arg, 62), // 3  unflagged
            (Arg, 0),  // 4  unflagged
            (Con, p),  // 5
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(MAX_ARG - 1);
        let mut sub = Substitution::new(MAX_ARG - 1);
        sub.set_arg(MAX_ARG - 1, Addr(5));

        build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(heap[q..], [(Comp, 3), (Con, p), (Arg, 62), (Arg, 0)]);
    }

    /// The meta mask survives the recursive descent through a bound arg.
    ///
    /// `build_arg` recurses into `build` when a substituted arg holds an
    /// address, and it forwards `meta_vars` when it does. If it forwarded
    /// `None` instead, any `Arg` inside that term would be substituted away
    /// rather than preserved, silently grounding part of the learned clause.
    ///
    /// In today's metarules a meta var always binds to a predicate symbol — a
    /// bare constant with nothing underneath it — so this path is not currently
    /// reachable. The test exists to pin the intent before it becomes so, since
    /// nothing else in the suite distinguishes the two.
    #[test]
    fn meta_mask_is_forwarded_through_a_bound_arg() {
        let t = SymbolDB::set_const("t");
        let s = SymbolDB::set_const("s");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 2), // 1: template t(A0)
            (Con, t),  // 2
            (Arg, 0),  // 3
            (Comp, 2), // 4: the term A0 is bound to, s(A1)
            (Con, s),  // 5
            (Arg, 1),  // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0); // A0 is a meta var; A1 is an ordinary clause var
        let mut sub = Substitution::default();
        sub.set_arg(0, Addr(4));

        build(&mut heap, &mut sub, Some(meta_vars), 1);

        assert_eq!(
            heap[q..],
            [(Comp, 2), (Con, t), (Comp, 2), (Con, s), (Arg, 1)]
        );
        assert_eq!(
            sub.get_arg(1),
            None,
            "a non-meta arg must not be allocated a variable, however deep it sits"
        );
    }

    //---------------------------------------------------------------------
    // Hypothesis clauses: query space -> query space
    //---------------------------------------------------------------------
    //
    // Learned clauses are the one place `Arg` cells live in mutable memory.
    // They are produced by `build(.., Some(meta_vars), ..)` into `cells`, and
    // when such a clause is later selected as a candidate its literals are read
    // straight back out of `cells` — source and destination in the same buffer.
    //
    // They can also hold `Ref` cells, because a substituted meta var may emit
    // one. `next_cell` dereferences refs and inlines whatever they point at, so
    // a ref that is bound by the time the clause is read materialises its value
    // into the new term. That is how a constant enters a learned clause: the
    // clause is stored holding a variable, and reading it later yields the
    // constant that variable acquired.
    //
    // A consequence worth stating plainly: a hypothesis clause's meaning is not
    // fixed when it is stored, only when it is read.

    /// A bound ref materialises its value. This is the constant-introduction
    /// mechanism.
    #[test]
    fn hypothesis_ref_bound_to_const_materialises_it() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 1: learned literal p(A0, R0)
            (Con, p),  // 2
            (Arg, 0),  // 3
            (Ref, 0),  // 4
            (Con, a),  // 5: the value R0 acquired
        ]);
        heap.var_regs = vec![Addr(q + 4).into()];
        let mut sub = Substitution::default();

        let built = build(&mut heap, &mut sub, None, q);

        assert_eq!(built, q + 5);
        assert_eq!(heap[built..], [(Comp, 3), (Con, p), (Ref, 1), (Con, a)]);
        assert!(
            !heap.contains_args(built),
            "read back as a goal, the clause is fully resolved"
        );
    }

    /// An unbound ref survives as a ref, so the clause keeps a variable there.
    #[test]
    fn hypothesis_ref_unbound_stays_a_ref() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 1: p(A0, R0)
            (Con, p),  // 2
            (Arg, 0),  // 3
            (Ref, 0),  // 4
        ]);
        heap.var_regs = vec![VarReg::UNBOUND];
        let mut sub = Substitution::default();

        let built = build(&mut heap, &mut sub, None, q);

        assert_eq!(heap[built..], [(Comp, 3), (Con, p), (Ref, 1), (Ref, 0)]);
    }

    /// A ref bound to another variable emits the representative it derefs to,
    /// not the variable written in the template.
    #[test]
    fn hypothesis_ref_bound_to_var_collapses_to_representative() {
        let p = SymbolDB::set_const("p");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 1: p(A0, R0)
            (Con, p),  // 2
            (Arg, 0),  // 3
            (Ref, 0),  // 4
        ]);
        // R0 -> R1, and R1 is unbound.
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let mut sub = Substitution::default();

        let built = build(&mut heap, &mut sub, None, q);

        assert_eq!(heap[built..], [(Comp, 3), (Con, p), (Ref, 2), (Ref, 1)]);
    }

    /// A ref bound into the *program* heap has its target copied into query
    /// space rather than being left as a reference.
    ///
    /// Retaining the program address would in fact be safe — program cells are
    /// immutable and outlive every query — so this pins the current copying
    /// behaviour in case that ever looks like an optimisation worth taking.
    #[test]
    fn hypothesis_ref_bound_to_program_constant() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(), // 0
            (Con, a), // 1: a program constant
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 2: p(A0, R0)
            (Con, p),  // 3
            (Arg, 0),  // 4
            (Ref, 0),  // 5
        ]);
        heap.var_regs = vec![Addr(1).into()];
        let mut sub = Substitution::default();

        let built = build(&mut heap, &mut sub, None, q);

        assert_eq!(heap[built..], [(Comp, 3), (Con, p), (Ref, 1), (Con, a)]);
    }

    /// The same bound ref appearing twice yields two independent copies of its
    /// value, not one shared subterm.
    ///
    /// Sound, since nothing is destructively updated, but a learned clause that
    /// mentions a large term twice pays for it twice.
    #[test]
    fn hypothesis_ref_to_structure_is_copied_per_occurrence() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 1: p(R0, R0)
            (Con, p),  // 2
            (Ref, 0),  // 3
            (Ref, 0),  // 4
            (Tup, 2),  // 5: the value R0 acquired
            (Con, a),  // 6
            (Con, b),  // 7
        ]);
        heap.var_regs = vec![Addr(q + 4).into()];
        let mut sub = Substitution::default();

        let built = build(&mut heap, &mut sub, None, q);

        assert_eq!(
            heap[built..],
            [
                (Comp, 3),
                (Con, p),
                (Tup, 2),
                (Con, a),
                (Con, b),
                (Tup, 2),
                (Con, a),
                (Con, b),
            ]
        );
        assert_eq!(heap.term_string(built), "p((a,b),(a,b))");
    }

    /// Refs and args in one literal, built both ways.
    ///
    /// The clearest statement of what `meta_vars` controls: the ref
    /// materialises identically in both builds, while the arg is resolved by
    /// the goal build and preserved by the template build.
    #[test]
    fn hypothesis_refs_and_args_built_as_goal_and_as_template() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 3), // 1: p(A1, R0)
            (Con, p),  // 2
            (Arg, 1),  // 3
            (Ref, 0),  // 4
            (Con, a),  // 5
        ]);
        heap.var_regs = vec![Addr(q + 4).into()];
        let mut sub = Substitution::default();

        let as_goal = build(&mut heap, &mut sub, None, q);
        let as_template = build(&mut heap, &mut sub, Some(BitFlag64::default()), q);

        assert_eq!(
            heap[as_goal..],
            [
                // as a goal: the arg is resolved
                (Comp, 3),
                (Con, p),
                (Ref, 1),
                (Con, a),
                // as a template: the arg is preserved, the ref is not
                (Comp, 3),
                (Con, p),
                (Arg, 1),
                (Con, a),
            ]
        );
        assert!(!heap.contains_args(as_goal));
        assert!(heap.contains_args(as_template));
    }

    /// The same template read before and after its ref is bound produces
    /// different terms.
    ///
    /// A stored hypothesis clause is not a snapshot; it is a view over live
    /// variable registers. Backtracking, which unbinds and truncates, therefore
    /// changes what an already-stored clause means.
    #[test]
    fn hypothesis_ref_binding_is_time_dependent() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![poison()]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([
            (Comp, 2), // 1: p(R0)
            (Con, p),  // 2
            (Ref, 0),  // 3
            (Con, a),  // 4
        ]);
        heap.var_regs = vec![VarReg::UNBOUND];
        let mut sub = Substitution::default();

        let before = build(&mut heap, &mut sub, None, q);
        heap.bind(0, Addr(q + 3));
        let after = build(&mut heap, &mut sub, None, q);

        assert_eq!(heap[before..before + 3], [(Comp, 2), (Con, p), (Ref, 0)]);
        assert_eq!(heap[after..], [(Comp, 2), (Con, p), (Con, a)]);
        assert_ne!(
            heap[before..before + 3],
            heap[after..],
            "the clause means something different once its variable is bound"
        );
    }

    // ---------------------------------------------------------------------
    // Group D: end-to-end, driven by the real `unify`.
    //
    // Groups A-C hand-construct substitutions, which proves `build` does what
    // it is told but not that it is ever told the right thing. These tests run
    // the sequence `env.rs` actually runs -- unify, then
    // `re_build_bound_arg_terms`, then `build` for each body literal -- so the
    // contract between `unify` and `build` is exercised rather than assumed.
    // ---------------------------------------------------------------------

    /// `p(A0) :- q(A0).` resolved against `p(X)`.
    ///
    /// The simplest handoff: unify binds the clause arg straight to the goal's
    /// variable, no term is copied, and the body literal must come out sharing
    /// that same variable.
    #[test]
    fn clause_head_arg_bound_to_goal_var_then_body_built() {
        let p = SymbolDB::set_const("p");
        let q_sym = SymbolDB::set_const("q");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: head p(A0)
            (Con, p),     // 2
            (Arg, 0),     // 3
            (Comp, 2),    // 4: body q(A0)
            (Con, q_sym), // 5
            (Arg, 0),     // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        // Goal p(X) in query space.
        heap.cells.extend([(Comp, 2), (Con, p), (Ref, 0)]);
        heap.var_regs = vec![VarReg::UNBOUND];

        let mut sub = unify(&mut heap, 1, q,31).expect("p(A0) must unify with p(X)");

        // `Arg` against `Ref` records a variable binding, not an address, so
        // nothing was bound in the heap and there is nothing to rebuild.
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert!(sub.is_empty(), "no heap variable was bound");

        re_build_bound_arg_terms(&mut heap, &mut sub);
        let goal = build(&mut heap, &mut sub, None, 4);

        assert_eq!(goal, q + 3);
        assert_eq!(heap[goal..], [(Comp, 2), (Con, q_sym), (Ref, 0)]);
        assert!(!heap.contains_args(goal));
    }

    /// `p([A0]) :- q(A0), r(A0).` resolved against `p(X)`.
    ///
    /// The flagship path. Unifying a structure against an unbound goal variable
    /// binds that variable to the *head* address -- which lives in the immutable
    /// program heap and still contains `Arg` cells. `re_build_bound_arg_terms`
    /// must copy it into query space, and the fresh variable it allocates for
    /// `A0` must be the same one both body literals see.
    #[test]
    fn head_structure_binds_goal_var_triggering_rebuild() {
        let p = SymbolDB::set_const("p");
        let q_sym = SymbolDB::set_const("q");
        let r = SymbolDB::set_const("r");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: head p([A0])
            (Con, p),     // 2
            LIS,          // 3
            (Arg, 0),     // 4
            EMPTY_LIS,    // 5
            (Comp, 2),    // 6: body q(A0)
            (Con, q_sym), // 7
            (Arg, 0),     // 8
            (Comp, 2),    // 9: body r(A0)
            (Con, r),     // 10
            (Arg, 0),     // 11
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells.extend([(Comp, 2), (Con, p), (Ref, 0)]);
        heap.var_regs = vec![VarReg::UNBOUND];

        let mut sub = unify(&mut heap, 1, q,31).expect("p([A0]) must unify with p(X)");

        // X is bound to the list *in the program heap*, and that list is
        // flagged for rebuild because it contains an `Arg`.
        assert_eq!(&sub[..], &[0]);
        assert_eq!(&sub.needs_rebuild[..], &[true]);
        assert_eq!(heap.var_regs[0].get_bind(), Some(Addr(3)));
        assert!(
            heap.var_regs[0].value() < prog.len(),
            "before the rebuild X points into program space"
        );

        re_build_bound_arg_terms(&mut heap, &mut sub);

        let rebuilt = q + 3;
        assert_eq!(heap.var_regs[0].get_bind(), Some(Addr(rebuilt)));
        assert!(
            heap.var_regs[0].value() >= prog.len(),
            "after the rebuild X must point into query space"
        );
        assert_eq!(sub.get_arg(0), Some(Var(1)), "A0 got a fresh query variable");

        let g1 = build(&mut heap, &mut sub, None, 6);
        let g2 = build(&mut heap, &mut sub, None, 9);
        assert_eq!((g1, g2), (rebuilt + 3, rebuilt + 6));

        assert_eq!(
            heap[rebuilt..],
            [
                LIS,
                (Ref, 1),
                EMPTY_LIS, // X = [_1]
                (Comp, 2),
                (Con, q_sym),
                (Ref, 1), // q(_1)
                (Comp, 2),
                (Con, r),
                (Ref, 1), // r(_1)
            ]
        );
        assert!(
            !heap.contains_args(rebuilt) && !heap.contains_args(g1) && !heap.contains_args(g2),
            "nothing reachable from the query may still be an Arg"
        );
    }

    /// `p([A0], b)` resolved against `p(X, Z)`.
    ///
    /// Two bindings made by the same `unify`, only one of which is flagged.
    /// Documents the asymmetry: an unflagged binding is left pointing into the
    /// program heap on purpose, because a ground program term is safe to share.
    #[test]
    fn flagged_bindings_are_copied_unflagged_ones_stay_shared() {
        let p = SymbolDB::set_const("p");
        let b = SymbolDB::set_const("b");

        let prog = prog(vec![
            poison(),  // 0
            (Comp, 3), // 1: p([A0], b)
            (Con, p),  // 2
            LIS,       // 3
            (Arg, 0),  // 4
            EMPTY_LIS, // 5
            (Con, b),  // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        heap.cells
            .extend([(Comp, 3), (Con, p), (Ref, 0), (Ref, 1)]);
        heap.var_regs = vec![VarReg::UNBOUND; 2];

        let mut sub = unify(&mut heap, 1, q,31).expect("p([A0], b) must unify with p(X, Z)");

        assert_eq!(&sub[..], &[0, 1]);
        assert_eq!(&sub.needs_rebuild[..], &[true, false]);

        // The invariant `re_build_bound_arg_terms` relies on when it reaches
        // past `bound()` straight into `var_regs[..].value()`.
        for i in 0..sub.len() {
            if sub.needs_rebuild[i] {
                assert!(
                    heap.var_regs[sub[i]].addr(),
                    "a flagged variable must hold an address, not a variable id"
                );
            }
        }

        re_build_bound_arg_terms(&mut heap, &mut sub);

        let rebuilt = q + 4; // the four-cell goal sits between q and here
        assert_eq!(heap.var_regs[0].get_bind(), Some(Addr(rebuilt)));
        assert_eq!(heap[rebuilt..], [LIS, (Ref, 2), EMPTY_LIS]);
        assert_eq!(
            heap.var_regs[1].get_bind(),
            Some(Addr(6)),
            "an Arg-free binding is left pointing at the shared program term"
        );
    }

    /// `p(A0) :- q(A0).` resolved against `p([a])`.
    ///
    /// The opposite direction to D2: the goal supplies the structure and the
    /// clause arg binds to it. The body build must then splice a copy of the
    /// goal's term in place of `A0`.
    #[test]
    fn head_arg_binds_to_goal_structure_and_flows_into_body() {
        let p = SymbolDB::set_const("p");
        let q_sym = SymbolDB::set_const("q");
        let a = SymbolDB::set_const("a");

        let prog = prog(vec![
            poison(),     // 0
            (Comp, 2),    // 1: head p(A0)
            (Con, p),     // 2
            (Arg, 0),     // 3
            (Comp, 2),    // 4: body q(A0)
            (Con, q_sym), // 5
            (Arg, 0),     // 6
        ]);
        let mut heap = QueryHeap::new(&prog, None);
        let q = prog.len();

        // Goal p([a]) -- fully ground, in query space.
        heap.cells
            .extend([(Comp, 2), (Con, p), LIS, (Con, a), EMPTY_LIS]);

        let mut sub = unify(&mut heap, 1, q,31).expect("p(A0) must unify with p([a])");

        assert_eq!(sub.get_arg(0), Some(Addr(q + 2)), "A0 points at the goal's list");
        assert!(sub.is_empty(), "no heap variable was bound");

        re_build_bound_arg_terms(&mut heap, &mut sub);
        let goal = build(&mut heap, &mut sub, None, 4);

        assert_eq!(goal, q + 5);
        assert_eq!(
            heap[goal..],
            [(Comp, 2), (Con, q_sym), LIS, (Con, a), EMPTY_LIS]
        );
        assert_eq!(heap.term_string(goal), "q([a])");
        assert!(heap.var_regs.is_empty(), "a ground resolution allocates no variables");
    }
}
